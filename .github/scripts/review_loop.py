#!/usr/bin/env python3
"""Portable GitHub-to-Hive review-loop router.

The cx53 self-hosted runners deliberately have a small host tool surface.  This
helper uses only Python's standard library and the credentials GitHub Actions
already injects; it does not depend on ``gh``, ``jq``, or a package manager.

Commands:

``route``
    Route one native Codex result: a submitted findings review goes to the
    burn seat (``REVIEW_BURN_ACTOR``, default ``talos``);
    a bot-authored clean PR comment — in either verdict format Codex emits —
    goes to the authoring seat.  A Codex comment that looks like a verdict but
    cannot be routed is reported to Hive rather than dropped.  At the
    exhaustion gate the authoring seat gets the human gate and Theoros
    additionally gets a retrospective wake carrying the per-round history.
``nudge``
    Add one ``@codex review`` comment (with an exact-head marker) per stalled,
    unreviewed head until the bounded automatic loop is exhausted, and
    re-deliver a standing verdict once per authoritative same-head verdict
    whose seat never acted.  A wake fires exactly once from an event-driven
    path; a consumed
    wake with no new GitHub event is otherwise silence forever.  The scheduled
    exhaustion path posts the same human gate as ``route`` but does not wake
    Theoros: the retrospective requires findings still present on the exact
    current head, and this branch is entered only because that head has none.
    This leg also chases a requested retrospective that never reached the PR —
    on every open PR, and on those closed within the last
    ``RETROSPECTIVE_CLOSED_SWEEP_HOURS`` hours, because a retrospective gates no
    closure and so routinely outlives the PR that owes it.
``canary``
    Post a harmless burn-seat liveness wake for end-to-end verification.
``terminal``
    Emit the closing belt span for a seat-authored PR: rounds consumed,
    rounds to CLEAN, findings burned, whether the bound was reached, and the
    SHA that landed.  Routes nothing and wakes nobody.
``terminal-sweep``
    Re-emit the closing span for recent FORK-originated closures, which the
    ``pull_request`` event cannot export because it holds no repository
    secrets.  Runs on the schedule, in the base repository's own context.
    Spans are keyed on the closure, so overlapping the event is harmless.

Every command exports its decisions to Logfire as OTLP/HTTP JSON spans when
``LOGFIRE_TOKEN`` is set (KRA-1132).  Telemetry is subordinate to routing: with
no token, or with a failing exporter, the belt behaves exactly as it did before
and says so on stderr.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from collections.abc import Callable, Iterable, Iterator, Mapping, Sequence
from contextlib import contextmanager
from datetime import datetime, timedelta, timezone
from typing import Any, NamedTuple

CODEX_LOGIN = "chatgpt-codex-connector[bot]"
WORKFLOW_LOGIN = "github-actions[bot]"
# The Codex-connected account the scheduled path and every seat's ``gh``
# authenticate as (KRA-1032).  The workflow sets ``CODEX_REVIEW_AUTHOR`` to
# this same login; the default is here so a seat running the helper from a
# shell (readiness limb 2) reads the belt's trust rule, not a narrower one.
CODEX_REVIEW_AUTHOR = "RationallyPrime"
MAX_REVIEW_ROUNDS = 7
REVIEW_STALL_SECONDS = 20 * 60
# Deliberately separate from REVIEW_STALL_SECONDS: that window bounds how long a
# head may wait for a *verdict*, while this one bounds how long a delivered
# verdict may sit unacted.  Burns routinely run past twenty minutes, so reusing
# the nudge window would wake a working seat mid-burn every scan.  At an hour,
# the worst case is one redundant wake, which seat dedupe doctrine makes safe.
WAKE_REDELIVERY_SECONDS = 60 * 60
DIGEST_CHUNK_BUDGET = 12000
# Per-span cap on enumerated finding locations; the counts stay exact.
FINDING_SPAN_BUDGET = 50
# A history location renders as ``path:line — identity``.  One definition of
# the join, so the site can always be read back out of it (``location_site``).
LOCATION_IDENTITY_SEPARATOR = " — "
ROUND_LOCATION_LINE_BUDGET = 8000
# The complete set of ``ensure_comment_at_head`` outcomes that mean "the marker
# this head needs is on the PR".  Every other value the helper returns is the
# chokepoint's own refusal reason, so readers derive the positive from this set
# and refuse on everything else — including a reason added later.  Collapsing
# refusals into one sentinel is what let a merge race be recorded as a push.
COMMENT_AT_HEAD_PUBLISHED = frozenset({"existing", "posted"})
# How long a requested retrospective may go undelivered before the loop chases
# it, and how many chases it gets.  Separate from WAKE_REDELIVERY_SECONDS even
# at the same value: that one bounds an unacted *verdict*, this one bounds an
# unwritten *testimony*, and a retrospective is written by hand against a
# seven-round history — the two windows will not stay equal.  Paid for on
# sokrates#1113, where the verdict was written to a file on cx53, posted with
# `--body @path` (which `gh` does not expand), and sat undelivered for 8 days
# with nothing in the loop noticing.
RETROSPECTIVE_DELIVERY_SECONDS = 60 * 60
RETROSPECTIVE_CHASE_ATTEMPTS = 2
# How far back the scheduled leg reconciles pending retrospectives on CLOSED
# pull requests.  Closure inside a delivery window is a normal outcome — the
# retrospective is testimony and gates nothing, so the exhaustion gate leaves
# the close to a human — and the open-PR enumeration cannot see it afterwards.
# Both windows sit within ~2h of the request, so this is not sized for the
# work: it is sized for the schedule, which GitHub throttles to a fire every
# ten hours or so under load, and which must still find the row when it runs.
RETROSPECTIVE_CLOSED_SWEEP_HOURS = 48
# Machine markers are versioned (KRA-1122 class): writers emit the ``v2:``
# forms below, and every reader also accepts the unversioned legacy form so
# markers already standing on open PRs keep suppressing what they suppressed.
# A policy-bearing marker (exhaustion) additionally records the policy value
# in force when it was written; a reader whose current policy differs must
# not treat it as terminal — the stale-three-round-marker incident.
MARKER_SCHEMA_VERSION = "v2"
# The retrospective receipt's version is ``v1`` rather than
# MARKER_SCHEMA_VERSION because verdict files already carry that form
# (sokrates#1113); see RETROSPECTIVE_MARKER_RE for the reader's leniency.
RETROSPECTIVE_MARKER_VERSION = "v1"
MARKER_NAMESPACE = "<!-- weave-review-loop:"
# Who writes a marker family.  ``seat-typed``: a seat writes it by hand from a
# doctrine template, so the template the doctrine shows, the writer here and
# the reader here must agree.  ``helper-minted``: only the helper writes it;
# doctrine may describe it but never asks a seat to type it.
SEAT_TYPED = "seat-typed"
HELPER_MINTED = "helper-minted"


class MarkerTemplate(NamedTuple):
    """One canonical marker string and the writer that emits it.

    ``template`` is the string with ``<slot>`` placeholders for what the writer
    takes as arguments; ``writer_args`` are those placeholders in the writer's
    positional order, so ``writer(*writer_args) == template`` is checkable.
    """

    template: str
    writer: str
    writer_args: tuple[str, ...]


# How a declared reader is applied, so a test can drive the PRODUCTION reader
# — the function the loop itself calls on the path that consumes the marker —
# rather than an adapter written for the test.  Every family declares at
# least one, and a family whose reader parses fields declares the parser, so
# a swapped or dropped field fails the round trip, not only a missed prefix.
#   ``head-forms``      ``reader(*args, head)`` returns the forms (a pattern,
#                       a literal, or a sequence) ``marker_comment_exists``
#                       consumes.
#   ``head-predicate``  ``reader(*args, comments, head)`` is the verdict.
#   ``slot-forms``      ``reader(*args, head, *slots)`` returns the forms
#                       ``marker_comment_exists`` consumes, ``slots`` being
#                       the instantiated values of ``fields`` (a chase's
#                       attempt, whose timestamp restarts the window).
#   ``slot-predicate``  ``reader(comments, head, *slots)`` is the verdict,
#                       ``slots`` being the instantiated values of ``fields``
#                       (the redelivery marker's verdict time).
#   ``head-map``        ``reader(*args, comments)`` maps head → the parsed
#                       value of ``fields[0]`` (a head-base pin's ref or SHA).
#   ``head-value``      ``reader(*args, comments, head)`` returns the parsed
#                       value of ``fields[0]`` (a chase's attempt), or the
#                       literal ``expect`` when the marker carries no slot
#                       (an exhaustion gate reads ``terminal``).
#   ``value``           ``reader(*args, comments)`` returns one PR-level
#                       value — the policy the exhaustion gate recorded —
#                       compared to the literal ``expect``; nothing to
#                       return without the marker.
#   ``verdict-parser``  ``reader(*args, comments)`` yields ``(comment,
#                       parsed)`` pairs; ``parsed["head"]`` is the exact head
#                       and the parsed fields are checked by name.
READER_VALUE = "value"
READER_HEAD_FORMS = "head-forms"
READER_SLOT_FORMS = "slot-forms"
READER_HEAD_PREDICATE = "head-predicate"
READER_SLOT_PREDICATE = "slot-predicate"
READER_HEAD_MAP = "head-map"
READER_HEAD_VALUE = "head-value"
# ``reader(*args, comments, head)`` → the trusted comment's timestamp, or None.
READER_HEAD_TIME = "head-time"
# ``reader(*args, comments, head, *slots)`` → the trusted comment's timestamp, or None.
READER_SLOT_TIME = "slot-time"
READER_VERDICT_PARSER = "verdict-parser"
# The placeholders doctrine may use for the head slot; every other placeholder
# keeps its own identity, so a template that swaps two roles is not the
# canonical one.  A real 40-hex head in an example is the head slot too.
MARKER_HEAD_ALIASES = ("<head>", "<40-hex-head>", "<sha>")


class MarkerReader(NamedTuple):
    """One production reader of a family and how the round trip applies it.

    ``name`` is the function the loop calls on the path that consumes the
    marker — never a wrapper added for the inventory; ``kind`` is one of the
    ``READER_*`` constants; ``args`` are positional arguments before the
    comments/head (the disposition kind for the shared head-disposition
    reader); ``fields`` names the template slots the reader parses, in the
    order the kind expects them; ``expect`` is the literal a slotless
    ``head-value`` reader must return.
    """

    name: str
    kind: str
    args: tuple[str, ...] = ()
    fields: tuple[str, ...] = ()
    expect: str | None = None


class MarkerFamily(NamedTuple):
    """One declared marker family: classification, templates, and its readers."""

    family: str
    classification: str
    templates: tuple[MarkerTemplate, ...]
    readers: tuple[MarkerReader, ...]


# THE marker inventory (KRA-1363).  Every family the helper writes or reads is
# declared here exactly once, with its classification, the canonical string a
# writer emits (and, for a seat-typed family, the string a seat types) and the
# production reader that accepts it.  The ``*_MARKER_PREFIX`` constants below
# are derived from it, so a family cannot exist in code without a
# classification, and the doctrine tests read this table rather than
# discovering templates in prose: writer, reader and prose are each checked
# against the one declaration, never against each other's spelling.
MARKER_INVENTORY: tuple[MarkerFamily, ...] = (
    MarkerFamily(
        "exhausted",
        HELPER_MINTED,
        (
            MarkerTemplate(
                f"{MARKER_NAMESPACE}exhausted:{MARKER_SCHEMA_VERSION}:<head>"
                f":max-rounds={MAX_REVIEW_ROUNDS} -->",
                "exhaustion_marker",
                ("<head>",),
            ),
        ),
        (
            MarkerReader(
                "exhaustion_marker_state", READER_HEAD_VALUE, expect="terminal"
            ),
            MarkerReader(
                "exhaustion_marker_bound", READER_VALUE, expect=str(MAX_REVIEW_ROUNDS)
            ),
            MarkerReader("exhaustion_gate_recorded", READER_VALUE, expect="True"),
        ),
    ),
    MarkerFamily(
        "nudge",
        HELPER_MINTED,
        (
            MarkerTemplate(
                f"{MARKER_NAMESPACE}nudge:{MARKER_SCHEMA_VERSION}:<head> -->",
                "nudge_marker",
                ("<head>",),
            ),
            # The form a workflow run actually posts: stamped with its numeric
            # run id.  A literal id, because the writer drops anything that is
            # not digits — a placeholder would test the fallback, not the stamp.
            MarkerTemplate(
                f"{MARKER_NAMESPACE}nudge:{MARKER_SCHEMA_VERSION}:<head>:run-12345 -->",
                "nudge_marker",
                ("<head>", "12345"),
            ),
        ),
        (
            MarkerReader("nudge_marker_pattern", READER_HEAD_FORMS),
            MarkerReader("bare_nudge_covers_head", READER_HEAD_PREDICATE),
        ),
    ),
    MarkerFamily(
        "redelivered",
        HELPER_MINTED,
        (
            MarkerTemplate(
                f"{MARKER_NAMESPACE}redelivered:{MARKER_SCHEMA_VERSION}"
                ":<head>:<verdict-at> -->",
                "redelivery_marker",
                ("<head>", "<verdict-at>"),
            ),
        ),
        (
            MarkerReader(
                "redelivery_recorded", READER_SLOT_PREDICATE, fields=("<verdict-at>",)
            ),
        ),
    ),
    MarkerFamily(
        "head-base",
        HELPER_MINTED,
        (
            MarkerTemplate(
                f"{MARKER_NAMESPACE}head-base:{MARKER_SCHEMA_VERSION}"
                ":<head>:<base-ref>:<base-sha> -->",
                "head_base_marker",
                ("<head>", "<base-ref>", "<base-sha>"),
            ),
        ),
        (
            MarkerReader("head_base_marker_for", READER_HEAD_FORMS),
            MarkerReader("head_base_recorded", READER_HEAD_PREDICATE),
            MarkerReader(
                "recorded_head_bases", READER_HEAD_MAP, fields=("<base-sha>",)
            ),
            MarkerReader(
                "recorded_head_base_refs", READER_HEAD_MAP, fields=("<base-ref>",)
            ),
        ),
    ),
    MarkerFamily(
        "product-gate",
        SEAT_TYPED,
        (
            MarkerTemplate(
                f"{MARKER_NAMESPACE}product-gate:{MARKER_SCHEMA_VERSION}:<head> -->",
                "product_gate_marker",
                ("<head>",),
            ),
        ),
        (
            MarkerReader(
                "head_disposition_pattern", READER_HEAD_FORMS, ("product-gate",)
            ),
            MarkerReader("head_disposed_at", READER_HEAD_TIME, ("product-gate",)),
        ),
    ),
    MarkerFamily(
        "noise",
        SEAT_TYPED,
        (
            MarkerTemplate(
                f"{MARKER_NAMESPACE}noise:{MARKER_SCHEMA_VERSION}:<head> -->",
                "noise_marker",
                ("<head>",),
            ),
        ),
        (
            MarkerReader("head_disposition_pattern", READER_HEAD_FORMS, ("noise",)),
            MarkerReader("head_disposed_at", READER_HEAD_TIME, ("noise",)),
        ),
    ),
    MarkerFamily(
        "hold",
        SEAT_TYPED,
        (
            MarkerTemplate(
                f"{MARKER_NAMESPACE}hold:{MARKER_SCHEMA_VERSION}:<head> -->",
                "hold_marker",
                ("<head>",),
            ),
        ),
        (
            MarkerReader("head_is_held", READER_HEAD_PREDICATE),
            MarkerReader("head_disposed_at", READER_HEAD_TIME, ("hold",)),
        ),
    ),
    MarkerFamily(
        "skip",
        SEAT_TYPED,
        (
            MarkerTemplate(
                f"{MARKER_NAMESPACE}skip:{MARKER_SCHEMA_VERSION}:<head> -->",
                "skip_marker",
                ("<head>",),
            ),
        ),
        (
            MarkerReader("head_is_skipped", READER_HEAD_PREDICATE),
            MarkerReader("head_disposed_at", READER_HEAD_TIME, ("skip",)),
        ),
    ),
    MarkerFamily(
        "retrospective",
        SEAT_TYPED,
        (
            MarkerTemplate(
                f"{MARKER_NAMESPACE}retrospective:{RETROSPECTIVE_MARKER_VERSION}"
                ":<head> -->",
                "retrospective_marker",
                ("<head>",),
            ),
        ),
        (MarkerReader("retrospective_delivered", READER_HEAD_PREDICATE),),
    ),
    MarkerFamily(
        "retrospective-wake",
        HELPER_MINTED,
        (
            MarkerTemplate(
                f"{MARKER_NAMESPACE}retrospective-wake:{MARKER_SCHEMA_VERSION}"
                ":<head> -->",
                "retrospective_wake_marker",
                ("<head>",),
            ),
        ),
        (
            MarkerReader("retrospective_wake_marker_pattern", READER_HEAD_FORMS),
            MarkerReader("retrospective_requested", READER_HEAD_PREDICATE),
            MarkerReader("retrospective_requested_at", READER_HEAD_TIME),
        ),
    ),
    MarkerFamily(
        "retrospective-chase",
        HELPER_MINTED,
        (
            MarkerTemplate(
                f"{MARKER_NAMESPACE}retrospective-chase:{MARKER_SCHEMA_VERSION}"
                ":<head>:attempt=<attempt> -->",
                "retrospective_chase_marker",
                ("<head>", "<attempt>"),
            ),
        ),
        (
            MarkerReader(
                "retrospective_chase_attempts", READER_HEAD_VALUE, fields=("<attempt>",)
            ),
            MarkerReader(
                "retrospective_chase_marker_pattern",
                READER_SLOT_FORMS,
                fields=("<attempt>",),
            ),
            MarkerReader(
                "retrospective_chased_at", READER_SLOT_TIME, fields=("<attempt>",)
            ),
        ),
    ),
    MarkerFamily(
        "substitute-summon",
        HELPER_MINTED,
        (
            MarkerTemplate(
                f"{MARKER_NAMESPACE}substitute-summon:<head> -->",
                "substitute_summon_marker",
                ("<head>",),
            ),
        ),
        (MarkerReader("substitute_summon_covers_head", READER_HEAD_PREDICATE),),
    ),
    MarkerFamily(
        "substitute-verdict",
        SEAT_TYPED,
        (
            MarkerTemplate(
                f"{MARKER_NAMESPACE}substitute-verdict:<head>:<actor>:clean -->",
                "substitute_verdict_clean_marker",
                ("<head>", "<actor>"),
            ),
            MarkerTemplate(
                f"{MARKER_NAMESPACE}substitute-verdict:<head>:<actor>"
                ":findings:<p1>:<p2>:<p3> -->",
                "substitute_verdict_findings_marker",
                ("<head>", "<actor>", "<p1>", "<p2>", "<p3>"),
            ),
        ),
        (
            MarkerReader(
                "substitute_verdicts",
                READER_VERDICT_PARSER,
                fields=("<head>", "<actor>", "<p1>", "<p2>", "<p3>"),
            ),
            MarkerReader(
                "substitute_verdict_marker_state", READER_VALUE, expect="present"
            ),
        ),
    ),
)


def index_marker_families(
    inventory: Sequence[MarkerFamily],
) -> dict[str, MarkerFamily]:
    """Family → declaration; a family declared twice is refused, not last-wins."""
    families: dict[str, MarkerFamily] = {}
    for entry in inventory:
        if entry.family in families:
            raise ValueError(
                f"marker family {entry.family!r} is declared twice in the inventory"
            )
        families[entry.family] = entry
    return families


MARKER_FAMILIES: dict[str, MarkerFamily] = index_marker_families(MARKER_INVENTORY)


def marker_prefix(family: str) -> str:
    """The comment-marker prefix of a DECLARED family; an undeclared one is an error."""
    if family not in MARKER_FAMILIES:
        raise KeyError(f"marker family {family!r} is not declared in MARKER_INVENTORY")
    return f"{MARKER_NAMESPACE}{family}:"


EXHAUSTED_MARKER_PREFIX = marker_prefix("exhausted")
NUDGE_MARKER_PREFIX = marker_prefix("nudge")
REDELIVERY_MARKER_PREFIX = marker_prefix("redelivered")
HEAD_BASE_MARKER_PREFIX = marker_prefix("head-base")
HEAD_BASE_MARKER_RE = re.compile(
    r"<!-- weave-review-loop:head-base:([^:\s]+):([^:\s]+) -->"
)
HEAD_BASE_MARKER_V2_RE = re.compile(
    r"<!-- weave-review-loop:head-base:v2:([^:\s]+):([^:\s]+):([^:\s]+) -->"
)
EXHAUSTED_MARKER_RE = re.compile(
    r"<!-- weave-review-loop:exhausted:"
    r"(?:v2:([^:\s]+):max-rounds=(\d+)|([^:\s]+)) -->"
)
PRODUCT_GATE_MARKER_PREFIX = marker_prefix("product-gate")
NOISE_MARKER_PREFIX = marker_prefix("noise")
HOLD_MARKER_PREFIX = marker_prefix("hold")
SKIP_MARKER_PREFIX = marker_prefix("skip")
# The head-disposition family: a trusted, once-per-head record that a seat
# stopped deliberately and left HEAD unchanged.  All three have the same
# shape, the same trust rule and the same meaning to the scheduled leg — the
# head's stillness is a decision, not a stall — so they are one reader over
# this table rather than one predicate each.  A fourth disposition is an entry
# here; it is not a fourth branch in ``_scan_open_pull`` (KRA-1326).
HEAD_DISPOSITION_PREFIXES: dict[str, str] = {
    "product-gate": PRODUCT_GATE_MARKER_PREFIX,
    "noise": NOISE_MARKER_PREFIX,
    "hold": HOLD_MARKER_PREFIX,
    "skip": SKIP_MARKER_PREFIX,
}
# The retrospective's own three markers.
#
# ``retrospective:`` is the only one the loop does not write: Theoros ends his
# verdict comment with it, and the loop reads it as the delivery receipt.  Its
# version is ``v1`` rather than MARKER_SCHEMA_VERSION because verdict files
# already carry that form (sokrates#1113); the reader accepts any ``v<n>:`` and
# the unversioned form, so a later bump needs no second reader.  It also accepts
# an abbreviated head of seven hex or more, because the cost of misreading a
# delivered verdict as missing is a wake and a PR line accusing a seat of
# silence it is not guilty of.  Unlike every other marker here it is trusted
# from ANY author: the retrospective is testimony a seat posts under its own
# credential, and there is no configured retrospective identity to check.
RETROSPECTIVE_MARKER_PREFIX = marker_prefix("retrospective")
RETROSPECTIVE_MARKER_RE = re.compile(
    r"<!-- weave-review-loop:retrospective:(?:v\d+:)?([0-9a-fA-F]{7,40}) -->"
)
# ``retrospective-wake:`` records that a retrospective was ASKED FOR at this
# head.  Without it the chase leg cannot tell an undelivered verdict from one
# nobody ever requested — the scheduled exhaustion path posts a gate and wakes
# nobody, and chasing that head would invent an obligation.
RETROSPECTIVE_WAKE_MARKER_PREFIX = marker_prefix("retrospective-wake")
# ``retrospective-chase:`` is the durable attempt counter.  Comments are the
# loop's only durable state, so the attempt bound has to live in one.
RETROSPECTIVE_CHASE_MARKER_PREFIX = marker_prefix("retrospective-chase")
# Every reader in this family accepts ``v<n>:`` rather than the one version its
# writer currently emits.  The writers below derive their version from
# MARKER_SCHEMA_VERSION, so a reader pinned to today's value stops recognising
# its own output the moment that constant advances — and each of the three
# markers fails a different way when it does.  Unread attempt counters read as
# zero and the bound is gone; an unread request receipt reads as "nobody asked"
# and the chase silently never fires; an unread chase timestamp reads as undated
# and the escalation stops.  A version bump means the marker's *shape* changed,
# and a shape change these patterns still match is one they can still read
# correctly, so accepting every version is the reading that follows the writer.
_RETROSPECTIVE_MARKER_VERSION_RE = r"v\d+:"
RETROSPECTIVE_CHASE_MARKER_RE = re.compile(
    r"<!-- weave-review-loop:retrospective-chase:"
    rf"{_RETROSPECTIVE_MARKER_VERSION_RE}([^:\s]+):attempt=(\d+) -->"
)
SUBSTITUTE_SUMMON_MARKER_PREFIX = marker_prefix("substitute-summon")
SUBSTITUTE_VERDICT_MARKER_PREFIX = marker_prefix("substitute-verdict")
# head : actor : clean | findings:<p1>:<p2>:<p3>.  The marker — not the prose
# around it — is the machine contract: substitute reviewers are seats, their
# prose formats drift, and parsing prose is the defect class the belt audit
# named.  Full 40-hex head only: a short sha cannot be exact-head evidence.
# The actor token is shared with ``normalize_substitute_actor`` so a configured
# seat cannot be summoned into an unparseable marker.
SUBSTITUTE_ACTOR_TOKEN = r"[a-z0-9-]+"
SUBSTITUTE_ACTOR_RE = re.compile(rf"^{SUBSTITUTE_ACTOR_TOKEN}$")
SUBSTITUTE_VERDICT_MARKER_RE = re.compile(
    r"<!-- weave-review-loop:substitute-verdict:"
    rf"([0-9a-fA-F]{{40}}):({SUBSTITUTE_ACTOR_TOKEN}):"
    r"(clean|findings:\d+:\d+:\d+) -->"
)
# The connector's account-wide quota refusal (2026-08-16 outage shape).  It is
# not CODEX_CONNECTOR_ERROR_PREFIX ("To use Codex here"), which is the
# unconnected-repo error; this one arrives on connected repos, auto-fires on
# pushes and comments, and means the find half is down until credits or reset.
CODEX_QUOTA_REFUSAL_PREFIX = "You have reached your Codex usage limits"
AI_USAGE_DEFAULT_THRESHOLD = 0.9
DEFAULT_SUBSTITUTE_ACTOR = "theoros"
# The find half and the burn twin are a CAST, not an anatomy: both seats are
# repo/org Actions variables (REVIEW_SUBSTITUTE_ACTOR / REVIEW_BURN_ACTOR)
# so a recast — e.g. 2026-08-18, Talos reviews and Theoros burns while
# Ariadne's usage is out — is a `gh variable set`, never a code sync.
DEFAULT_BURN_ACTOR = "talos"
# The retrospective seat is not cast the way the find half and burn twin are:
# the exhaustion retrospective is Theoros's charter (KRA-1029), not a role a
# repository fills.  One constant so the wake and the chase that follows it
# cannot address different seats.
RETROSPECTIVE_ACTOR = "theoros"
# ...and yet the SEAT is a cast (Hákon's ruling, 2026-09-07): for the
# thirteen-lanes crunch Theoros's exhaustion testimony is on hold, so
# ``REVIEW_RETROSPECTIVE_ACTOR`` names the seat (default: the constant above)
# or one of ``RETROSPECTIVE_HOLD_VALUES`` to post the gate and wake nobody.
RETROSPECTIVE_ACTOR_ENV = "REVIEW_RETROSPECTIVE_ACTOR"
RETROSPECTIVE_HOLD_VALUES = frozenset({"none", "held", "off"})
# The burn cast became a roster the same day (Talos dry for a day while the
# belt kept minting to it): ``REVIEW_BURN_ROSTER`` lists, in preference
# order, every seat that may burn, and the usage meter casts the first one
# whose pool reads available (the vendored seat-router below).  Unset, the
# single ``REVIEW_BURN_ACTOR`` cast stands, byte for byte.
BURN_ROSTER_ENV = "REVIEW_BURN_ROSTER"
BURN_THRESHOLD_ENV = "REVIEW_BURN_THRESHOLD"
SEAT_USAGE_PROFILES_ENV = "REVIEW_SEAT_USAGE_PROFILES"
# A burn wake carries the edge's per-delivery effort overlay (hive#49): a
# PR label ``effort:<tier>`` wins, else ``REVIEW_BURN_EFFORT``; the tier
# vocabulary is the union of the provider ladders and the edge clamps.
BURN_EFFORT_ENV = "REVIEW_BURN_EFFORT"
EFFORT_LABEL_PREFIX = "effort:"
WAKE_EFFORT_TIERS = ("low", "medium", "high", "xhigh", "max", "ultra")
FINDING_IDENTITY_MAX = 96
_IDENTITY_NOISE = re.compile(
    r"</?sub>|!\[[^\]]*\]\([^)]*\)|\[P[123]-[A-Za-z]+\]|\*{1,2}|_{1,2}"
)
UNRESOLVED_CLEAN_PREFIX = "unresolved-clean:"
# The clean-verdict literals and predicate are NOT declared here, and neither
# are the patterns that read a clean verdict's declared head.  They arrive in
# the vendored ``weave_reviewkit.verdicts`` region below, which is the single
# home for what "Codex said this head is clean" means (KRA-1222) — including
# which head it said it about.
CODEX_TASK_REPORT_HEADING = "### Summary"
CODEX_CONNECTOR_ERROR_PREFIX = "To use Codex here"
CODEX_COMMENT_CLEAN = "clean"
CODEX_COMMENT_TASK_VERDICT = "task-verdict"
CODEX_COMMENT_TASK_REPORT = "task-report"
CODEX_COMMENT_CONNECTOR_ERROR = "connector-error"
CODEX_COMMENT_QUOTA_REFUSAL = "quota-refusal"
CODEX_COMMENT_UNKNOWN = "unknown"
# KRA-1074 A1: the composed boundary is the merge authority for a seat-authored
# PR, and Hákon's word is retrospective (KRA-1083's digest). There is no label
# to consult and no prospective word to wait for, so every wake states the one
# regime rather than branching on a grant that no longer exists.
# The scope test every reviewer and burner applies BEFORE a finding is written
# or patched (Hákon's ruling, 2026-09-06, after sokrates#1186 turned a 20-line
# reset script into an eleven-round rewrite by burning every cell the reviewer
# produced). One constant, rendered at the top of the summon comment, the burn
# wake, the substitute-review wake and the retrospective wake, so the test is
# applied where the finding is born, not after it has cost a round.
# The trailer a burn (or any seat) commit carries to say the next round is not
# worth its hour: the push leg posts a `skip` disposition for that head instead
# of `@codex review`, the scheduled leg honours it like a hold, and the merge
# boundary reads the marker as the verdict limb (Hákon's ruling, 2026-09-06).
REVIEW_SKIP_TRAILER = "Review-skip:"
SCOPE_TEST = (
    "Round test — before another review round is summoned or burned, ask what "
    "the round buys. Hold the code to its purpose and use case: what is it for, "
    "who runs it, and where? If a defect still in it would announce itself the "
    "first time the code runs — a script failing on invocation, a test tripping, "
    "a request erroring — then execution is the review: skip the round, merge at "
    "green, run it. Spend a round only where a latent defect would stay silent — "
    "durable state, data loss, a wrong answer that reads as right, a customer "
    "boundary. Nothing here is live on a customer box and the product is still "
    "being built; an hour of the Weave saved outweighs a finding the first run "
    "would have found for free."
)
SCOPE_TEST_REVIEWER = (
    f"{SCOPE_TEST} Raise only findings the first run would not have found."
)
SCOPE_TEST_BURNER = (
    f"{SCOPE_TEST} The convention: ask this once round two's verdict is in — "
    "before round three is summoned — and at every round after; earlier, skip "
    "only a trivial one-line repair. If every remaining defect would surface on "
    f"first run, do not re-summon: end your burn commit with the trailer "
    f"`{REVIEW_SKIP_TRAILER} <one line why>`; the push records the skip and the "
    "head merges at green with zero threads."
)

MERGE_REGIME = (
    "Merge authority: the composed boundary itself — this exact head "
    "review-closed, required checks green, no conflicts. No label and no "
    "prospective word gates it; Hákon's veto is retrospective, and the "
    "machine-merge digest carries the merge to him."
)
# Sentinel: ``find_half_route`` / ``_scan_open_pull`` fetch the meter themselves
# unless the scheduled scan supplies the one reading it already took.
_FETCH_METER = object()
SEAT_ACTORS = {
    "Fable": "fable",
    "Ariadne": "ariadne",
    "gnomon": "gnomon",
    "Talos": "talos",
    "Theoros": "theoros",
}
# A repository may map extra git author names onto a seat that shepherds
# them (``REVIEW_AUTHOR_ALIASES="Some Author=fable"``). Two cases force
# this: a model that is not a seat writes the code (commits land under a
# human identity), and GitHub's "Update branch" writes a merge commit
# under the clicker's git name, so HEAD is no longer a seat and the
# scan's seat gate returns ``(0, 0, 0)`` in silence. An alias names who
# receives the wake; it never invents a new seat.
#
# A git author name is unauthenticated metadata that anyone can set, so
# an alias is honoured ONLY when the PR head lives in the base
# repository — a branch only collaborators can push. Without that fence
# a stranger's fork PR against a public repo could spell the aliased
# name into a commit and help itself to the reviewer budget.
AUTHOR_ALIASES_ENV = "REVIEW_AUTHOR_ALIASES"
# The roster of seats this script can route a wake to, and the accept-set an
# alias destination is checked against. The actor grammar is a *transport*
# constraint: it decides whether a token can ride a WAKE envelope and a
# verdict marker, not whether anyone answers it. ``Someone=ghost`` satisfies
# the grammar, so grammar alone leaves the "never invents a new seat" promise
# above unenforced — the alias admits that author's head into the loop,
# spends a review on it, then dead-letters ``WAKE: ghost``.
#
# The three role casts (``REVIEW_SUBSTITUTE_ACTOR`` / ``REVIEW_BURN_ACTOR`` /
# ``SKILL_AUDIT_ACTOR``) deliberately stay grammar-only. They name a seat by
# ROLE, and a seat that reviews or burns need not author anything, so it need
# not appear in ``SEAT_ACTORS`` — which is an authorship map. An alias is the
# one configuration whose destination is by definition an already-known seat.
KNOWN_SEAT_ACTORS = frozenset(SEAT_ACTORS.values())
# Skill documents are exempt from the review loop (Hákon's ruling,
# 2026-08-21): per-PR prose review of a skill never converges — wd#117 and
# wd#119 each burned the full seven-round bound on oscillating P2 prose
# findings — so skills get the weekly one-pass audit (`skill-audit` command)
# instead of Codex rounds. A PR is exempt only when EVERY touched path,
# including a rename's old name, sits under one of these corpus roots.
#
# These three roots serve the audit sweep alone. The loop exemption is wider
# (Hákon's ruling, 2026-09-03): recipe YAML and law primitives are corpora
# of the same kind, each with a mechanical CI gate that is its whole quality
# bar, and their roots are repository-specific — so the adopting repo names
# them in ``REVIEW_LOOP_EXEMPT_PATHS`` (see ``loop_exempt_prefixes``) and
# the shared helper never hard-codes one repo's layout. The weekly audit is
# a prose pass and never sweeps those extra roots.
SKILL_PATH_PREFIXES = ("skills/", ".agents/skills/", ".claude/skills/")
EXEMPT_PATHS_ENV = "REVIEW_LOOP_EXEMPT_PATHS"
# When the declared roots took effect, as an ISO-8601 instant. The workflow
# leaves it unset and the terminal legs read the variable's ``updated_at``
# instead; the offline backfill sets it because it resolves the declaration
# per repository and must not have the helper re-read one it already dated.
EXEMPT_PATHS_SINCE_ENV = "REVIEW_LOOP_EXEMPT_PATHS_SINCE"
DEFAULT_SKILL_AUDIT_ACTOR = "theoros"
SKILL_AUDIT_WORKFLOW_FILE = "skill-audit.yml"
# First-run / missing-workflow lookback. Consecutive runs watermark from the
# previous successful run of this workflow, so a delayed schedule cannot leave
# skill commits between two windows; 14 days is only the bootstrap overlap.
SKILL_AUDIT_FALLBACK_DAYS = 14
# How far back the scheduled terminal sweep looks for fork closures the
# ``pull_request`` event could not export.  Wider than any plausible schedule
# gap on purpose: re-emitting a closure already exported is free (the span
# carries the closure's own id and every query groups on it), while missing one
# is a permanent hole in the distribution.
BELT_SWEEP_WINDOW_HOURS = 168
# REST pull-request reviews have ``submitted_at`` and no ``updated_at``.
# GraphQL ``lastEditedAt`` is the edit clock ``at_closure`` needs.
_REVIEW_LAST_EDITED_QUERY = """
query ($owner: String!, $name: String!, $number: Int!, $cursor: String) {
  repository(owner: $owner, name: $name) {
    pullRequest(number: $number) {
      reviews(first: 100, after: $cursor) {
        nodes { id lastEditedAt }
        pageInfo { hasNextPage endCursor }
      }
    }
  }
}
""".strip()
_EDIT_STAMP_KEYS = ("updated_at", "lastEditedAt", "last_edited_at")
# Copied onto a snapshot item whose current body is later than the closure
# boundary.  The original text is not recoverable from the API; consumers
# must not parse that body as as-of-closure evidence.  Identity (id, author,
# head, review association, path, line) still is.
BODY_AS_OF_CLOSURE = "body_as_of_closure"
# A Codex review submitted before closure whose summary was edited after it and
# which has no surviving inline findings.  Its id, head and ``submitted_at``
# prove a round was consumed; its verdict is unrecoverable, so it is neither
# ``clean`` nor ``findings`` and never closes review.
UNKNOWN_REVIEW_RESULT = "unknown"


def required_env(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise RuntimeError(f"required environment variable {name} is missing")
    return value


class ApiHttpError(RuntimeError):
    """HTTP failure with a machine-checkable status and bounded message."""

    def __init__(self, method: str, path: str, status_code: int) -> None:
        self.status_code = status_code
        super().__init__(f"{method} {path} failed with HTTP {status_code}")


class JsonApi:
    """Small authenticated JSON HTTP client with bounded error output."""

    def __init__(
        self,
        base_url: str,
        token: str,
        *,
        authorization_scheme: str = "Bearer",
        extra_headers: Mapping[str, str] | None = None,
    ) -> None:
        self.base_url = base_url.rstrip("/")
        self.token = token
        self.authorization_scheme = authorization_scheme
        self.extra_headers = dict(extra_headers or {})

    def request(
        self,
        method: str,
        path: str,
        *,
        payload: Mapping[str, Any] | None = None,
        query: Mapping[str, Any] | None = None,
    ) -> Any:
        url = f"{self.base_url}/{path.lstrip('/')}"
        if query:
            url = f"{url}?{urllib.parse.urlencode(query)}"
        data = json.dumps(payload).encode() if payload is not None else None
        headers = {
            "Accept": "application/vnd.github+json",
            "Authorization": f"{self.authorization_scheme} {self.token}",
            "Content-Type": "application/json; charset=utf-8",
            "User-Agent": "weave-doctrine-review-loop",
            **self.extra_headers,
        }
        request = urllib.request.Request(url, data=data, headers=headers, method=method)
        try:
            with urllib.request.urlopen(request, timeout=30) as response:
                raw = response.read()
        except urllib.error.HTTPError as error:
            # Never echo response bodies: they can contain private PR text or
            # provider diagnostics.  The status and endpoint are enough to act.
            raise ApiHttpError(method, path, error.code) from error
        except urllib.error.URLError as error:
            raise RuntimeError(f"{method} {path} failed: {error.reason}") from error
        return json.loads(raw) if raw else None


class GitHubApi(JsonApi):
    def __init__(self, token: str, repository: str) -> None:
        super().__init__(
            os.environ.get("GITHUB_API_URL", "https://api.github.com"),
            token,
            extra_headers={"X-GitHub-Api-Version": "2022-11-28"},
        )
        self.repository = repository

    def repo_path(self, suffix: str) -> str:
        return f"repos/{self.repository}/{suffix.lstrip('/')}"

    def authenticated_login(self) -> str:
        user = self.request("GET", "user")
        if not isinstance(user, Mapping) or not str(user.get("login") or "").strip():
            raise RuntimeError("GitHub authenticated-user lookup returned no login")
        return str(user["login"])

    def get(self, suffix: str, *, query: Mapping[str, Any] | None = None) -> Any:
        return self.request("GET", self.repo_path(suffix), query=query)

    def post(self, suffix: str, payload: Mapping[str, Any]) -> Any:
        return self.request("POST", self.repo_path(suffix), payload=payload)

    def paginate(
        self, suffix: str, *, query: Mapping[str, Any] | None = None
    ) -> list[Any]:
        items: list[Any] = []
        page = 1
        while True:
            page_query = {**dict(query or {}), "per_page": 100, "page": page}
            batch = self.get(suffix, query=page_query)
            if not isinstance(batch, list):
                raise TypeError(f"GET {suffix} did not return a list")
            items.extend(batch)
            if len(batch) < 100:
                return items
            page += 1

    def graphql(
        self, query: str, variables: Mapping[str, Any] | None = None
    ) -> Mapping[str, Any]:
        result = self.request(
            "POST",
            "graphql",
            payload={"query": query, "variables": dict(variables or {})},
        )
        if not isinstance(result, Mapping):
            raise TypeError("POST graphql did not return an object")
        if result.get("errors"):
            # Never echo the payload: GraphQL errors can quote private titles.
            raise RuntimeError("POST graphql returned errors")
        data = result.get("data")
        if not isinstance(data, Mapping):
            raise TypeError("POST graphql returned no data")
        return data

    def review_last_edited_at(self, pr_number: int) -> dict[str, str]:
        """GraphQL ``lastEditedAt`` keyed by REST ``node_id``.

        REST ``pulls/{n}/reviews`` has ``submitted_at`` and no ``updated_at``,
        even though the summary body remains editable.  GraphQL ``databaseId``
        is a 32-bit int and overflows real review ids, so the opaque ``id``
        (REST ``node_id``) is the join.  A never-edited review is omitted
        (null ``lastEditedAt``).
        """
        owner, sep, name = self.repository.partition("/")
        if not sep or not owner or not name:
            raise RuntimeError(
                f"repository {self.repository!r} is not owner/name for GraphQL"
            )
        times: dict[str, str] = {}
        cursor: str | None = None
        while True:
            data = self.graphql(
                _REVIEW_LAST_EDITED_QUERY,
                {
                    "owner": owner,
                    "name": name,
                    "number": int(pr_number),
                    "cursor": cursor,
                },
            )
            repository = data.get("repository")
            if not isinstance(repository, Mapping):
                return times
            pull_request = repository.get("pullRequest")
            if not isinstance(pull_request, Mapping):
                return times
            connection = pull_request.get("reviews")
            if not isinstance(connection, Mapping):
                return times
            nodes = connection.get("nodes")
            if isinstance(nodes, list):
                for node in nodes:
                    if not isinstance(node, Mapping):
                        continue
                    node_id = node.get("id")
                    edited = node.get("lastEditedAt")
                    if (
                        isinstance(node_id, str)
                        and node_id.strip()
                        and isinstance(edited, str)
                        and edited.strip()
                    ):
                        times[node_id] = edited
            page = connection.get("pageInfo")
            if not (
                isinstance(page, Mapping)
                and page.get("hasNextPage")
                and isinstance(page.get("endCursor"), str)
                and page["endCursor"]
            ):
                return times
            cursor = str(page["endCursor"])


class SlackApi(JsonApi):
    def __init__(self, token: str, channel: str) -> None:
        super().__init__(
            "https://slack.com/api",
            token,
            extra_headers={"Accept": "application/json"},
        )
        self.channel = channel

    def post_message(self, text: str, *, thread_ts: str | None = None) -> str:
        payload: dict[str, Any] = {"channel": self.channel, "text": text}
        if thread_ts:
            payload["thread_ts"] = thread_ts
        result = self.request(
            "POST",
            "chat.postMessage",
            payload=payload,
        )
        if not isinstance(result, dict) or result.get("ok") is not True:
            error = (
                result.get("error", "unknown_error")
                if isinstance(result, dict)
                else "invalid_response"
            )
            raise RuntimeError(f"Slack chat.postMessage failed: {error}")
        ts = result.get("ts")
        if not isinstance(ts, str) or not ts:
            raise RuntimeError("Slack chat.postMessage returned no ts")
        return ts


INERT_WAKE_QUOTE = "> "
EVIDENCE_HEADING_SEPARATOR = "\n## "


def neutralize_wake_lines(text: str) -> str:
    """Quote every line Hive's ``parseAddressedWake`` would read as an envelope.

    Evidence published before the commit-point WAKE must be inert: the parser
    scans every line of every message — thread replies included — so an
    embedded ``WAKE: talos`` inside a quoted finding body would dispatch the
    seat against a partially published digest, the exact race the
    evidence-first protocol exists to close.
    """
    lines: list[str] = []
    for line in text.splitlines():
        stripped = line.strip()
        upper = stripped.upper()
        if upper.startswith(("WAKE:", "NEXT ")):
            lines.append(f"{INERT_WAKE_QUOTE}{line}")
        else:
            lines.append(line)
    return "\n".join(lines)


def wake_instruction(message: str) -> str:
    """The instruction half of a wake message — everything before the evidence.

    Every chunked wake builder ends its header with exactly one ``## `` evidence
    heading (a doctrine test pins this for both builders); the digest blocks
    after it are data, not instruction.  The commit-point message must carry the
    full instruction — the skill tag, the verdict counts, the coordinates, and
    the doctrine text — because the addressed message is the only one the seat
    is dispatched on; a commit point reduced to coordinates dispatches a burn
    with zero findings in its instruction body.
    """
    return message.split(EVIDENCE_HEADING_SEPARATOR, 1)[0].rstrip()


def evidence_root_notice(envelope: str, chunk_count: int) -> str:
    """The inert thread root. Must never start a line with WAKE:/NEXT."""
    return (
        f"Review-loop: publishing {chunk_count} evidence message(s) for "
        f"`{envelope}` in this thread. The addressed wake posts LAST, after "
        "every evidence message lands; until then nothing in this thread is a "
        "dispatch, and a failed publication leaves no wake at all."
    )


def publication_commit_message(chunk_count: int, header: str) -> str:
    """The final addressed message — the dispatch commit point.

    Carries the wake's full instruction (envelope, skill tag, verdict counts,
    coordinates, doctrine), stripped only of the digest blocks: those are the
    evidence messages above it in the thread, which the seat reads as data.
    """
    return (
        f"{wake_instruction(header)}\n\n"
        f"Evidence publication complete — the full digest is the {chunk_count} "
        "evidence message(s) above in this thread (envelope lines quoted "
        "inert). Read the whole thread before acting; this message is the "
        "dispatch commit point."
    )


# ---------------------------------------------------------------------------
# Belt telemetry.
#
# The belt is a governed actor: its identity is its span (INV-13).  Export is
# OTLP/HTTP JSON straight to Logfire so the helper keeps the zero-dependency
# property every adopting repository relies on.  Telemetry is strictly
# subordinate to routing: a failed export prints one bounded diagnostic and the
# wake still goes out.
# ---------------------------------------------------------------------------

# Logfire write tokens are region-scoped and carry their region in the token
# itself.  Posting a token's spans to the other region is a 401 that fail-open
# telemetry can only whisper about on stderr, so read the region off the
# credential rather than making every adopting repository configure it — and
# refuse a region this map does not know rather than guessing one, because a
# guess is exactly that silent 401 with the diagnostic spent on the wrong host.
LOGFIRE_REGION_RE = re.compile(r"^pylf_v\d+_(?P<region>[a-z]+)_")
LOGFIRE_REGION_URLS = {
    "us": "https://logfire-us.pydantic.dev",
    "eu": "https://logfire-eu.pydantic.dev",
}
BELT_SERVICE_NAME = "review-loop"
TELEMETRY_TIMEOUT_SECONDS = 5
OTLP_STATUS_OK = 1
OTLP_STATUS_ERROR = 2


def script_fingerprint() -> str:
    """Identify this vendored copy of the helper.

    Adopting repositories carry their own copy of this file, so a belt-health
    dashboard cannot assume one version.  The digest of the running source is
    the only identifier that cannot drift from what actually ran.
    """
    try:
        with open(__file__, "rb") as source:
            return hashlib.sha256(source.read()).hexdigest()[:12]
    except OSError:
        return "unknown"


def logfire_base_url(token: str) -> str:
    """The ingest host this write token belongs to; ``""`` when unsupported.

    A token whose region this map does not resolve — an unreadable shape, or a
    region Logfire added after this helper was vendored — has no host that can
    accept it.  Naming one anyway sends every span to a host that answers 401,
    so the empty string is the honest answer and the caller refuses.
    """
    match = LOGFIRE_REGION_RE.match(token)
    if match is None:
        return ""
    return LOGFIRE_REGION_URLS.get(match.group("region"), "")


def otlp_any_value(value: Any) -> dict[str, Any] | None:
    """Encode one attribute value; ``None`` means "not measured", never null."""
    if isinstance(value, bool):
        return {"boolValue": value}
    if isinstance(value, int):
        return {"intValue": str(value)}
    if isinstance(value, float):
        return {"doubleValue": value}
    if isinstance(value, str):
        return {"stringValue": value}
    if isinstance(value, (list, tuple)):
        encoded = [otlp_any_value(item) for item in value]
        return {
            "arrayValue": {"values": [item for item in encoded if item is not None]}
        }
    return None


def otlp_attributes(attributes: Mapping[str, Any]) -> list[dict[str, Any]]:
    encoded: list[dict[str, Any]] = []
    for key, value in attributes.items():
        any_value = otlp_any_value(value)
        if any_value is not None:
            encoded.append({"key": key, "value": any_value})
    return encoded


def post_otlp_json(url: str, payload: bytes, headers: Mapping[str, str]) -> None:
    request = urllib.request.Request(
        url, data=payload, headers=dict(headers), method="POST"
    )
    with urllib.request.urlopen(request, timeout=TELEMETRY_TIMEOUT_SECONDS):
        return


class BeltSpan:
    """One belt decision, recorded as an OTLP span."""

    def __init__(
        self,
        name: str,
        *,
        trace_id: str,
        span_id: str,
        parent_span_id: str,
        attributes: Mapping[str, Any],
        start_ns: int,
    ) -> None:
        self.name = name
        self.trace_id = trace_id
        self.span_id = span_id
        self.parent_span_id = parent_span_id
        self.attributes: dict[str, Any] = dict(attributes)
        self.start_ns = start_ns
        self.end_ns = start_ns
        self.status_code = OTLP_STATUS_OK
        self.status_message = ""

    def set(self, **attributes: Any) -> None:
        self.attributes.update(attributes)

    def fail(self, error: BaseException) -> None:
        # Bounded, type-led text: belt errors are already scrubbed of response
        # bodies, and telemetry must not become a second leak channel.
        self.status_code = OTLP_STATUS_ERROR
        self.status_message = f"{type(error).__name__}: {error}"[:200]

    def to_otlp(self) -> dict[str, Any]:
        span: dict[str, Any] = {
            "traceId": self.trace_id,
            "spanId": self.span_id,
            "name": self.name,
            "kind": 1,
            "startTimeUnixNano": str(self.start_ns),
            "endTimeUnixNano": str(self.end_ns),
            "attributes": otlp_attributes(
                {
                    "logfire.msg": str(self.attributes.get("logfire.msg", self.name)),
                    "logfire.span_type": "span",
                    **self.attributes,
                }
            ),
            "status": {"code": self.status_code},
        }
        if self.status_message:
            span["status"]["message"] = self.status_message
        if self.parent_span_id:
            span["parentSpanId"] = self.parent_span_id
        return span


class BeltTelemetry:
    """Collect belt spans for one hook invocation and export them once.

    Every public method is fail-open.  Routing wakes are the belt's job;
    telemetry is evidence about that job and never gates it.  Failures stay
    visible on stderr (R-3) instead of being swallowed silently.
    """

    def __init__(
        self,
        *,
        token: str = "",
        endpoint: str = "",
        repository: str = "",
        command: str = "",
        run_id: str = "",
        transport: Any = None,
    ) -> None:
        self.token = token
        self.endpoint = endpoint
        self.repository = repository
        self.command = command
        self.run_id = run_id
        self.transport = transport or post_otlp_json
        self.trace_id = os.urandom(16).hex()
        self.spans: list[BeltSpan] = []
        self._open_span_ids: list[str] = []

    @classmethod
    def from_env(cls, command: str, *, transport: Any = None) -> BeltTelemetry:
        token = os.environ.get("LOGFIRE_TOKEN", "").strip()
        # An explicit base URL still wins: a proxy or a self-hosted collector
        # is a deployment choice the token cannot describe.
        base_url = os.environ.get("LOGFIRE_BASE_URL", "").strip().rstrip("/")
        if token and not base_url:
            base_url = logfire_base_url(token)
            if not base_url:
                print(
                    "belt telemetry disabled: LOGFIRE_TOKEN names no supported "
                    f"ingest region (known: {', '.join(sorted(LOGFIRE_REGION_URLS))}); "
                    "set LOGFIRE_BASE_URL to export it.",
                    file=sys.stderr,
                )
                token = ""
        return cls(
            token=token,
            endpoint=f"{base_url}/v1/traces" if base_url else "",
            repository=os.environ.get("GITHUB_REPOSITORY", ""),
            command=command,
            run_id=os.environ.get("GITHUB_RUN_ID", ""),
            transport=transport,
        )

    @classmethod
    def disabled(cls) -> BeltTelemetry:
        """A telemetry object with no token: collects nothing, exports nothing."""
        return cls()

    @property
    def enabled(self) -> bool:
        return bool(self.token)

    def _record(
        self, name: str, attributes: Mapping[str, Any], *, start_ns: int
    ) -> BeltSpan:
        return BeltSpan(
            name,
            trace_id=self.trace_id,
            span_id=os.urandom(8).hex(),
            parent_span_id=self._open_span_ids[-1] if self._open_span_ids else "",
            attributes={"repository": self.repository, **attributes},
            start_ns=start_ns,
        )

    @contextmanager
    def span(self, name: str, **attributes: Any) -> Iterator[BeltSpan]:
        """Open a timed span; the body's exceptions are recorded and re-raised."""
        record = self._record(name, attributes, start_ns=time.time_ns())
        self._open_span_ids.append(record.span_id)
        try:
            yield record
        except BaseException as error:
            record.fail(error)
            raise
        finally:
            self._open_span_ids.pop()
            record.end_ns = time.time_ns()
            self.spans.append(record)

    def event(self, name: str, **attributes: Any) -> BeltSpan:
        """Record one belt decision as a point span under the current span."""
        record = self._record(name, attributes, start_ns=time.time_ns())
        self.spans.append(record)
        return record

    def head_commit_age_seconds(self, github: GitHubApi, head_sha: str) -> float | None:
        """Seconds between the head COMMIT's own date and now, or ``None``.

        Named for what it measures.  ``commit_time`` reads the committer/author
        date written by the client, not a server-observed push: a force-reset
        to an older commit, a cherry-pick with preserved timestamps, or a
        skewed clock all make this larger, smaller, or negative relative to
        routing latency, so it must never be read as one.

        Telemetry-only: this is the one attribute the belt does not already
        hold, so the lookup happens only when telemetry is enabled and any
        failure yields an absent measurement rather than a failed route.
        """
        if not self.enabled:
            return None
        try:
            commit = github.get(f"commits/{head_sha}")
            if not isinstance(commit, Mapping):
                return None
            now = datetime.now(timezone.utc)
            committed_at = commit_time(commit, now.isoformat())
            return (now - committed_at).total_seconds()
        except Exception as error:  # noqa: BLE001 - a measurement never fails a route.
            print(f"belt telemetry head age unavailable: {error}", file=sys.stderr)
            return None

    def envelope(self, spans: Sequence[BeltSpan]) -> dict[str, Any]:
        return {
            "resourceSpans": [
                {
                    "resource": {
                        "attributes": otlp_attributes(
                            {
                                "service.name": BELT_SERVICE_NAME,
                                "service.version": script_fingerprint(),
                            }
                        )
                    },
                    "scopeSpans": [
                        {
                            "scope": {"name": BELT_SERVICE_NAME},
                            "spans": [span.to_otlp() for span in spans],
                        }
                    ],
                }
            ]
        }

    def flush(self) -> None:
        """Export this invocation's spans once.  Never raises."""
        spans, self.spans = self.spans, []
        if not self.enabled or not spans:
            return
        try:
            self.transport(
                self.endpoint,
                json.dumps(self.envelope(spans)).encode(),
                {
                    "Content-Type": "application/json",
                    "Authorization": f"Bearer {self.token}",
                    "User-Agent": "weave-doctrine-review-loop",
                },
            )
        except Exception as error:  # noqa: BLE001 - telemetry never fails the belt.
            print(
                f"belt telemetry export failed: {type(error).__name__}: {error}",
                file=sys.stderr,
            )


_TELEMETRY = BeltTelemetry.disabled()


def belt() -> BeltTelemetry:
    """This invocation's telemetry sink; disabled until ``main`` installs one."""
    return _TELEMETRY


def install_belt_telemetry(telemetry: BeltTelemetry) -> BeltTelemetry:
    """Install the sink for this process: one hook run, one trace."""
    global _TELEMETRY
    _TELEMETRY = telemetry
    return telemetry


def verdict_event_time(raw: Any) -> str:
    """The SOURCE event's own instant, as a sortable UTC string.

    Export time is not verdict time.  A rerun of an older findings workflow
    publishes its span *after* a newer CLEAN already landed on the same
    unchanged head, so a query that orders by ``start_timestamp`` reads the
    superseded verdict as the head's latest and reports findings for a round
    the belt closed.  This is the key the dashboard's per-head reduction orders
    on, so it comes from the review or comment that produced the verdict.

    An event with no usable timestamp yields ``""`` rather than a floor value:
    a sentinel instant would sort as a real one, and an empty string is
    readable as the absence it is (it sorts last under ``desc``).
    """
    if not isinstance(raw, str) or not raw.strip():
        return ""
    try:
        parsed = parse_github_time(raw.strip())
    except ValueError:
        return ""
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return (
        parsed.astimezone(timezone.utc)
        .isoformat(timespec="microseconds")
        .replace("+00:00", "Z")
    )


def belt_verdict(
    *,
    pr_number: int,
    head_sha: str,
    verdict_kind: str,
    decision: str,
    source_event_at: Any,
    review_round: int,
    rounds_consumed: int,
    counts: Mapping[str, int] | None = None,
    findings: Sequence[Mapping[str, Any]] = (),
    author_seat: str = "",
    review_state: str = "",
    base_ref: str = "",
    base_sha: str = "",
    chunks: int | None = None,
    head_commit_age: float | None = None,
    substitute: str = "",
) -> None:
    """Record one round of the belt: the row a convergence query reads.

    Round-level attributes are the whole point of the instrument — a PR's
    rounds-to-CLEAN, its severity mix per round, and whether the same finding
    locations keep coming back are all one query over these spans.

    ``source_event_at`` is the raw GitHub timestamp of the review or comment
    this verdict was read from.  It is required, not defaulted: a call site
    that cannot name its source event cannot be ordered against a competing
    verdict on the same head, and a silent default would publish export time
    under a name that promises otherwise.
    """
    counts = counts or {"p1": 0, "p2": 0, "p3": 0, "total": 0}
    belt().event(
        "belt.verdict",
        **{
            "logfire.msg": (
                f"#{pr_number} round {review_round}/{MAX_REVIEW_ROUNDS}: "
                f"{verdict_kind} -> {decision}"
            ),
            "pull_request": pr_number,
            "head_sha": head_sha,
            "verdict_kind": verdict_kind,
            "decision": decision,
            # The source event's time, not the export's: what orders two
            # verdicts on one unchanged head.  See ``verdict_event_time``.
            "verdict_at": verdict_event_time(source_event_at),
            "round": review_round,
            "rounds_consumed": rounds_consumed,
            "max_review_rounds": MAX_REVIEW_ROUNDS,
            "findings_total": counts["total"],
            "findings_p1": counts["p1"],
            "findings_p2": counts["p2"],
            "findings_p3": counts["p3"],
            # Bounded: a round with hundreds of findings must not turn one
            # span into a megabyte of payload.  The count above stays exact.
            "finding_locations": [
                history_location(finding) for finding in findings[:FINDING_SPAN_BUDGET]
            ],
            "author_seat": author_seat,
            "review_state": review_state,
            "base_ref": base_ref,
            "base_sha": base_sha,
            "wake_chunks": chunks,
            "head_commit_age_seconds": head_commit_age,
            "substitute_actor": substitute,
        },
    )


def belt_ignored(reason: str, **attributes: Any) -> None:
    """Record a route that ended without a wake, and why."""
    belt().event(
        "belt.route.ignored",
        **{"logfire.msg": f"route ignored: {reason}", "reason": reason, **attributes},
    )


def publishable_at_head(
    github: GitHubApi,
    pr_number: int,
    head_sha: str,
    repository: str,
    *,
    decision: str,
    require_open: bool = True,
) -> bool:
    """Decide liveness at the publication itself, not at the route's first read.

    ``refresh_pr_at_head`` at the top of a route returns a snapshot, and the
    route then spends more round trips before it posts anything — the
    head-base pin, the stale-base and retarget probes, the head-commit age.
    A PR that merges inside that window is open at the route's read and merged
    at the publish, so the route-top read cannot be the only liveness
    decision: it has to be repeated at the boundary it protects.  That is the
    same argument that put liveness in the chokepoint rather than in per-path
    guards (KRA-1226) — applied to *where* the chokepoint is called from.

    ``require_open`` forwards the chokepoint's one documented waiver and
    defaults the same way, so a publication that waives closure at its route's
    first read can be re-decided here rather than falling back to a hand-rolled
    refresh — the head half of the decision is the half every publication
    needs, and it is the half a waiving caller would otherwise lose (KRA-1374).

    This narrows the window to one HTTP round trip; it does not close it.  A
    merge landing between this read and the post still publishes, and no
    check-then-act over a resource this process does not hold can do better.
    """
    return (
        refresh_pr_at_head(
            github,
            pr_number,
            head_sha,
            repository,
            action=f"{decision} publication",
            require_open=require_open,
            on_ignored=lambda reason: belt_ignored(
                reason,
                pull_request=pr_number,
                head_sha=head_sha,
                decision=decision,
            ),
        )
        is not None
    )


class PublicationWithheld(Exception):
    """The boundary refused between a wake's first Slack post and its dispatch.

    A multi-message wake dispatches a seat only with its final addressed
    message, so its check-to-publish window is the whole run of Slack requests
    before that message rather than one HTTP round trip.  Re-deciding liveness
    there can refuse *after* the inert root and the evidence chunks are
    already posted, and that is not a delivery failure: nothing was
    dispatched, the refusal is already recorded as ``belt.route.ignored``, and
    the run must not redden.

    Raised rather than returned so that a publication path which does not
    handle it fails visibly (R-3) instead of reporting a wake it never sent.
    """


def deliver_wake(
    post: Callable[[], Any],
    *,
    github: GitHubApi,
    repository: str,
    pr_number: int,
    head_sha: str,
    decision: str,
    chunks: int | None = None,
) -> bool:
    """Publish an already-recorded verdict's wake, and record what delivery did.

    This is the publication boundary for every wake the routes send, so it is
    where liveness is re-decided: ``github`` and ``repository`` are required,
    not optional, because a caller allowed to omit them is a path with no
    guard — the shape KRA-1226 deleted.  Returns whether the wake was posted;
    a refusal records ``belt.route.ignored`` with the chokepoint's reason and
    posts nothing.

    A ``post`` that runs the multi-message protocol carries a second boundary
    of its own and raises ``PublicationWithheld`` when it refuses there; that
    is the same refusal one HTTP hop later, so it answers ``False`` and
    records no delivery.

    The verdict and its delivery are two facts, and only the second one is
    transported.  Recording them together makes a Slack outage delete the
    first: the belt observed a Codex result, classified it, and acted on it,
    and a convergence query would read a round that never happened.  So every
    caller records ``belt.verdict`` (and, at the bound, ``belt.exhaustion``)
    *before* calling this, and this span carries delivery alone.

    Worse at the bound, which is why the ordering is not cosmetic: the gate
    comment is durable and posted first, so a later scheduled scan sees the
    existing gate and returns early — without a manual rerun those spans are
    never reconstructed, and the exhaustion is invisible forever.

    Re-raises (R-3): a failed wake must still redden the run.  What it must
    not do is take the observation down with it.
    """
    if not publishable_at_head(
        github, pr_number, head_sha, repository, decision=decision
    ):
        return False
    try:
        post()
    except PublicationWithheld:
        return False
    except Exception as error:
        belt().event(
            "belt.delivery",
            **{
                "logfire.msg": f"#{pr_number} {decision}: delivery FAILED",
                "pull_request": pr_number,
                "head_sha": head_sha,
                "decision": decision,
                "delivered": False,
                "delivery_error": f"{type(error).__name__}: {error}",
                "wake_chunks": chunks,
            },
        )
        raise
    belt().event(
        "belt.delivery",
        **{
            "logfire.msg": f"#{pr_number} {decision}: delivered",
            "pull_request": pr_number,
            "head_sha": head_sha,
            "decision": decision,
            "delivered": True,
            "delivery_error": "",
            "wake_chunks": chunks,
        },
    )
    return True


def post_threaded_messages(
    slack: SlackApi,
    messages: Sequence[str],
    *,
    github: GitHubApi,
    repository: str,
    pr_number: int,
    head_sha: str,
    decision: str,
) -> None:
    """Publish a wake atomically: evidence first, the addressed WAKE last.

    Hive binds a seat to the thread of a WAKE delivery, and it can claim the
    first addressed message before later chunks exist — so a multi-message
    wake posted WAKE-first can dispatch a seat against a partial digest, and
    a failed continuation leaves a live but incomplete instruction.

    A single-message wake needs no protocol and posts as before.  A chunked
    wake posts an inert thread root, then every chunk with its envelope lines
    neutralized, and only after all of them succeed a final small addressed
    message carrying the envelope and the belt subject.  Any earlier post
    failing raises out (R-3) and no WAKE is ever published.

    That final message is the dispatch, so liveness is re-decided immediately
    before it.  A single-message wake already has that property — its one post
    sits directly after its caller's own check — while a chunked wake spends
    one Slack request per chunk in between, so the caller's check protects the
    root and this one protects the dispatch.  On refusal the chunks stay
    posted and inert, no seat is dispatched, and ``PublicationWithheld`` says
    so.  The liveness arguments are required for the reason ``deliver_wake``'s
    are: a caller allowed to omit them is a publication with no guard.
    """
    if not messages:
        return
    if len(messages) == 1:
        slack.post_message(messages[0])
        return
    thread_ts = _post_inert_evidence(
        slack,
        messages,
        root_notice=evidence_root_notice(
            wake_envelope_line(messages[0]), len(messages)
        ),
    )
    if not publishable_at_head(
        github, pr_number, head_sha, repository, decision=decision
    ):
        print(
            f"withheld the addressed {decision} for {repository}#{pr_number} "
            f"(head={head_sha}): {len(messages)} evidence chunk(s) are posted "
            "and inert, and no seat was dispatched"
        )
        raise PublicationWithheld(decision)
    slack.post_message(
        publication_commit_message(len(messages), messages[0]),
        thread_ts=thread_ts,
    )


def _post_inert_evidence(
    slack: SlackApi, messages: Sequence[str], *, root_notice: str
) -> str:
    """Post the thread root and every neutralized chunk; dispatch nothing.

    Everything this posts is inert by construction: the root is a notice its
    caller composes, and each chunk has its envelope lines neutralized, so no
    seat is bound by any of it.  The addressed dispatch is assembled only by
    ``publication_commit_message``, whose single call site is the wake path
    above — that is what makes this helper safe to share rather than a second
    publication path with no check.
    """
    thread_ts = slack.post_message(root_notice)
    for message in messages:
        slack.post_message(neutralize_wake_lines(message), thread_ts=thread_ts)
    return thread_ts


def digest_root_notice(subject: str, chunk_count: int) -> str:
    """The inert thread root for a publication that dispatches nobody."""
    return (
        f"Review-loop: publishing the {subject} as {chunk_count} message(s) in "
        "this thread. Nothing here dispatches a seat: this is a report, and "
        "every routing envelope it quotes is inert."
    )


def digest_completion_notice(subject: str, chunk_count: int) -> str:
    """The final message of a no-dispatch publication.

    Deliberately *not* ``publication_commit_message``: that one carries the
    wake's own instruction live, because for a wake the last message **is** the
    dispatch.  A digest has no seat to dispatch, and its content is a merged
    pull request's prose — which in this estate routinely quotes ``WAKE:`` and
    ``NEXT`` lines — so reusing the commit point would let an informational
    report bind a seat.  This says the report is complete and carries no
    envelope of its own.
    """
    return (
        f"The {subject} above is complete — {chunk_count} message(s) in this "
        "thread. Report only: no seat is dispatched by any of them, and any "
        "routing envelope quoted inside them is quoted inert."
    )


def post_threaded_digest_without_a_pull_subject(
    slack: SlackApi, messages: Sequence[str], *, subject: str
) -> None:
    """The one publication with no pull request for the liveness rule to read.

    ``post_threaded_messages`` requires its five liveness arguments because a
    caller allowed to omit them is a publication with no guard.  The
    machine-merge digest is not that caller: it reports a *window* of merges
    across several repositories, so there is no single pull request it could be
    live at, and the rule cannot be evaluated there at all rather than being
    waived per path.  Enforcing it anyway deletes the leg — the same argument
    that gives ``refresh_pr_at_head`` its one ``require_open=False`` waiver for
    the retrospective chase, whose subject is likewise a dead PR.

    This is one documented exception, not an escape hatch: the digest's
    subjects are already merged, and nothing it posts routes a review round.
    ``test_the_merge_digest_is_the_only_publication_without_a_pull_subject``
    names any second caller that appears, in either script.

    Every message it posts is neutralized, the single-message path included:
    the content is authored prose from merged pull requests, so an envelope
    line inside it is the digest's own to quote inert.  Liveness is what this
    publication cannot check; inertness is what it must not skip.
    """
    if not messages:
        return
    if len(messages) == 1:
        slack.post_message(neutralize_wake_lines(messages[0]))
        return
    thread_ts = _post_inert_evidence(
        slack, messages, root_notice=digest_root_notice(subject, len(messages))
    )
    print(
        f"published the {subject} as {len(messages)} chunk(s); it reports a "
        "window of merges across repositories, so there is no pull request "
        "for the liveness rule to read"
    )
    slack.post_message(
        digest_completion_notice(subject, len(messages)),
        thread_ts=thread_ts,
    )


def load_event() -> dict[str, Any]:
    path = required_env("GITHUB_EVENT_PATH")
    with open(path, encoding="utf-8") as event_file:
        event = json.load(event_file)
    if not isinstance(event, dict):
        raise TypeError("GitHub event payload is not an object")
    return event


def commit_author_name(commit: Mapping[str, Any]) -> str:
    nested = commit.get("commit")
    if not isinstance(nested, Mapping):
        return ""
    author = nested.get("author")
    return str(author.get("name") or "") if isinstance(author, Mapping) else ""


def author_aliases() -> Mapping[str, str]:
    """Repository-configured ``git author name -> seat`` overlay.

    Parsed from ``REVIEW_AUTHOR_ALIASES`` as ``Name=seat`` pairs. A value
    that contains a newline is newline-separated (so a git author name
    may contain a comma); a single-line value is comma-separated.

    A destination is refused here, not discovered later as a
    dead-lettered wake, on two counts: it must be able to carry a wake
    (the actor grammar) *and* it must name a seat that exists
    (``KNOWN_SEAT_ACTORS``). Grammar alone would let ``Someone=ghost``
    admit that author's head into the loop and spend a review on it
    before the wake fell on the floor.
    """
    raw = os.environ.get(AUTHOR_ALIASES_ENV, "").strip()
    if not raw:
        return {}
    entries = raw.split("\n") if "\n" in raw else raw.split(",")
    aliases: dict[str, str] = {}
    for entry in entries:
        entry = entry.strip()
        if not entry:
            continue
        name, separator, seat = entry.partition("=")
        name, seat = name.strip(), seat.strip()
        if not separator or not name or not seat:
            raise ValueError(
                f"{AUTHOR_ALIASES_ENV} entry {entry!r} is not 'Author Name=seat'"
            )
        actor = normalize_substitute_actor(seat)
        if actor is None:
            raise ValueError(
                f"{AUTHOR_ALIASES_ENV} maps {name!r} to {seat!r}, which is "
                "outside the actor grammar [a-z0-9-]+ after normalization; "
                "refusing to wake an unroutable seat"
            )
        if actor not in KNOWN_SEAT_ACTORS:
            raise ValueError(
                f"{AUTHOR_ALIASES_ENV} maps {name!r} to {seat!r}, which is "
                "not a known seat "
                f"({', '.join(sorted(KNOWN_SEAT_ACTORS))}); an alias names "
                "who receives the wake, it never invents a seat"
            )
        aliases[name] = actor
    return aliases


def seat_map(*, same_repo: bool) -> Mapping[str, str]:
    """The author-to-seat map in force for one PR.

    ``same_repo=False`` (a fork head) sees the built-in seats only: an
    alias is a repository-scoped grant, and a fork branch is writable by
    anyone.
    """
    if not same_repo:
        return SEAT_ACTORS
    aliases = author_aliases()
    if not aliases:
        return SEAT_ACTORS
    return {**SEAT_ACTORS, **aliases}


def head_is_same_repo(pull_request: Mapping[str, Any]) -> bool:
    """True when the PR head branch lives in the base repository itself.

    Absence never reads as same-repo: a payload missing either side is
    treated as a fork, which costs at most one unrouted wake and never
    spends the reviewer budget on a branch a stranger controls.
    """

    def slug(side: str) -> str:
        section = pull_request.get(side)
        if not isinstance(section, Mapping):
            return ""
        repository = section.get("repo")
        if not isinstance(repository, Mapping):
            return ""
        return str(repository.get("full_name") or "")

    head, base = slug("head"), slug("base")
    return bool(head) and bool(base) and head == base


def head_is_not_base_repo(pull_request: Mapping[str, Any]) -> bool:
    """True when the PR payload shows the head lives outside the base repository.

    GitHub sets ``head.repo`` to JSON null when the fork is gone, and to the
    fork repository when it still exists.  Either fact is a foreign head.
    ``GitHubApi.get`` still requests ``commits/{sha}`` against the base, so
    this predicate alone does not license swallowing a 404 — a lost
    Contents grant is the same status.  A payload that omits ``head.repo``
    establishes neither, and must not suppress a 404.
    """
    head = pull_request.get("head")
    if not isinstance(head, Mapping) or "repo" not in head:
        return False
    repo = head["repo"]
    if repo is None:
        return True
    if not isinstance(repo, Mapping) or not str(repo.get("full_name") or ""):
        return False
    base = pull_request.get("base")
    if not isinstance(base, Mapping):
        return False
    base_repo = base.get("repo")
    if not isinstance(base_repo, Mapping):
        return False
    base_slug = str(base_repo.get("full_name") or "")
    if not base_slug:
        return False
    return str(repo.get("full_name") or "") != base_slug


def live_fork_full_name(pull_request: Mapping[str, Any]) -> str:
    """The live head-fork slug, or ``""`` when the fork is gone or is the base."""
    if not head_is_not_base_repo(pull_request):
        return ""
    head = pull_request.get("head")
    if not isinstance(head, Mapping):
        return ""
    repo = head.get("repo")
    if not isinstance(repo, Mapping):
        return ""
    return str(repo.get("full_name") or "").strip()


def contents_probe_ref(github: GitHubApi, pull_request: Mapping[str, Any]) -> str:
    """A ref established to exist now, never a historical ``base.sha``.

    A merged PR whose target branch was later deleted, or whose base
    history was force-rewritten, leaves ``base.sha`` unreadable even when
    the token still has Contents.  The live default branch is the
    currently-reachable commit that probe needs.
    """
    base = pull_request.get("base")
    if isinstance(base, Mapping):
        repo = base.get("repo")
        if isinstance(repo, Mapping):
            branch = str(repo.get("default_branch") or "").strip()
            if branch:
                return branch
    repository = str(getattr(github, "repository", "") or "").strip()
    request = getattr(github, "request", None)
    if not repository or not callable(request):
        return ""
    try:
        meta = request("GET", f"repos/{repository}")
    except ApiHttpError as error:
        if error.status_code == 404:
            return ""
        raise
    if not isinstance(meta, Mapping):
        raise TypeError("repository lookup did not return an object")
    return str(meta.get("default_branch") or "").strip()


def contents_authority_established(
    github: GitHubApi, pull_request: Mapping[str, Any]
) -> bool:
    """True when a currently-existing ref is readable via ``commits/{ref}``.

    ``GitHubApi.get`` always requests ``repos/{base}/commits/...``, so a 404
    on a foreign head is indistinguishable from a lost Contents grant
    until this probe succeeds.  A historical ``base.sha`` is not that
    probe: it can 404 after the target branch is deleted or the base is
    force-rewritten, and treating that as authorization failure re-UNREADs
    the repository for an otherwise tolerable deleted-fork head
    (KRA-1371).  The live default branch is a ref established to exist
    now.

    A payload/repo that names no default branch establishes nothing.  A
    404 on the probe is "contents not granted"; every other status still
    raises (R-3).  The ref is percent-encoded as one path component:
    ``JsonApi.request`` concatenates the suffix into a URL, so a raw
    ``#`` (or ``?``, ``/``) would be a fragment, query, or extra segment
    and a resulting 404 would be mistaken for missing Contents.
    """
    ref = contents_probe_ref(github, pull_request)
    if not ref:
        return False
    try:
        github.get(f"commits/{urllib.parse.quote(ref, safe='')}")
    except ApiHttpError as error:
        if error.status_code == 404:
            return False
        raise
    return True


def choose_author(
    names: Iterable[str],
    fallback: str = "",
    seats: Mapping[str, str] | None = None,
) -> str:
    """Choose the original non-burn-seat committer, then the burn seat, then HEAD author.

    Burn commits land on the PR branch under the burn seat's identity; the
    wake must still address the seat whose judgment the PR carries.
    """
    mapping = SEAT_ACTORS if seats is None else seats
    burn = burn_actor()
    first_burn = ""
    for name in names:
        if name in mapping and mapping[name] != burn:
            return name
        if name in mapping and not first_burn:
            first_burn = name
    return first_burn or fallback


def head_commit_author(
    github: GitHubApi,
    pr_number: int,
    head_sha: str,
    pull_request: Mapping[str, Any] | None = None,
) -> str:
    """The head commit's git author name, or ``""`` when nobody can fetch it.

    This lookup is reached only where the PR's own commit list named no
    seat, so it is the last thing that could name one -- and a head commit
    no one can fetch cannot be a seat's work.  A merged fork PR whose fork
    has since been deleted leaves exactly that: a head SHA the base
    repository no longer resolves.  Raising there aborts the caller, and
    the merge digest reads a whole repository under one ``try``, so a
    single stranger's merged PR would report the repository ``UNREAD``,
    fail the run, and hold the watermark behind that same row on every
    later digest (KRA-1371).

    A ``404`` on the base is not "nobody can fetch it" while the payload
    still names a live fork: ``GitHubApi.get`` never leaves the base, so
    a squash/rebase SHA that lives only on the fork is a miss, not an
    unreachable commit.  Prove Contents on a currently-existing ref,
    then ask ``head.repo.full_name``.  A built-in seat who authored that
    head (the commit list omitted them — the reason this fallback
    exists, including PRs past the commits-endpoint cap) must still be
    classified as a seat; otherwise the wake or merge-digest entry is
    dropped and the watermark advances.

    Returning a live-fork author and suppressing to "no author" share
    that Contents gate.  A public fork can succeed while the base
    Contents grant is gone; accepting that author would skip the PR,
    report the repository as read, and advance the watermark.  GitHub
    conceals a lost Contents grant as a 404 on ``commits/{sha}`` even
    when the token can still read pull requests, so a foreign-head 404
    without that probe is indistinguishable from authorization failure.
    Probing the historical ``base.sha`` is not that proof: a deleted
    target branch or a force-rewritten base 404s that SHA with Contents
    still granted.  Swallowing that 404 would skip a seat whose commit
    list named none, report the repository as read, and advance the
    watermark.  Every other status still raises, a 404 whose payload
    does not establish a foreign head still raises, a live-fork lookup
    that is not a 404 still raises, and a foreign-head 404 without
    contents authority still raises, so an authority or transient
    failure stays visible rather than quietly reading as "no seat"
    (R-3).
    """
    try:
        commit = github.get(f"commits/{head_sha}")
    except ApiHttpError as error:
        if error.status_code != 404:
            raise
        payload = pull_request
        if payload is None:
            fetched = github.get(f"pulls/{pr_number}")
            if not isinstance(fetched, Mapping):
                raise TypeError("pull request lookup did not return an object")
            payload = fetched
        if not head_is_not_base_repo(payload):
            raise
        if not contents_authority_established(github, payload):
            raise
        fork = live_fork_full_name(payload)
        if fork:
            try:
                commit = github.request("GET", f"repos/{fork}/commits/{head_sha}")
            except ApiHttpError as fork_error:
                if fork_error.status_code != 404:
                    raise
            else:
                if not isinstance(commit, Mapping):
                    raise TypeError("GitHub commit lookup returned an invalid response")
                return commit_author_name(commit)
        print(
            f"#{pr_number}: head commit {head_sha} is unreachable (HTTP 404) -- "
            "resolved as no authoring seat",
            file=sys.stderr,
        )
        return ""
    return commit_author_name(commit)


def author_for_pr(
    github: GitHubApi,
    pr_number: int,
    head_sha: str,
    pull_request: Mapping[str, Any] | None = None,
) -> tuple[str, str] | None:
    """Resolve the seat this PR's wakes address, or ``None`` for no seat.

    Aliases are resolved lazily and only where they can change the
    answer: a repository with no ``REVIEW_AUTHOR_ALIASES``, or a PR a
    built-in non-burn seat already authored, makes exactly the API calls
    it made before aliases existed. The PR-detail fetch that carries the
    fork fence therefore lands only on the PRs an alias could newly
    claim. Aliased non-burn authors beat a later burn commit — otherwise
    a burn on an aliased PR would steal the wake.
    """
    names = [
        commit_author_name(item)
        for item in github.paginate(f"pulls/{pr_number}/commits")
    ]
    burn = burn_actor()
    builtin = choose_author(names)
    if builtin and SEAT_ACTORS[builtin] != burn:
        return (builtin, SEAT_ACTORS[builtin])

    aliases = author_aliases()
    payload = pull_request
    if aliases:
        if payload is None:
            fetched = github.get(f"pulls/{pr_number}")
            if not isinstance(fetched, Mapping):
                raise TypeError("pull request lookup did not return an object")
            payload = fetched
        if head_is_same_repo(payload):
            seats = seat_map(same_repo=True)
            aliased = choose_author(names, seats=seats)
            if aliased and seats[aliased] != burn:
                return (aliased, seats[aliased])
            if not builtin:
                head_author = head_commit_author(github, pr_number, head_sha, payload)
                aliased = choose_author(
                    [*names, head_author], fallback=head_author, seats=seats
                )
                actor = seats.get(aliased)
                return (aliased, actor) if actor else None
            return (builtin, SEAT_ACTORS[builtin])

    if builtin:
        return (builtin, SEAT_ACTORS[builtin])
    # A queued review can outlive its HEAD SHA after a force-push or fork
    # deletion. Do not let a needless fallback lookup suppress a seat that
    # the surviving PR commit list already identified.
    author = head_commit_author(github, pr_number, head_sha, payload)
    actor = SEAT_ACTORS.get(author)
    return (author, actor) if actor else None


def loop_exempt_prefixes() -> tuple[str, ...]:
    """The corpus roots whose PRs skip the review loop in this repository.

    The skill roots are fixed (ruling 2026-08-21). A repository adds the
    roots of its other mechanically gated corpora — recipe YAML, law
    primitives (ruling 2026-09-03) — through ``REVIEW_LOOP_EXEMPT_PATHS``,
    comma-separated; unset or empty adds nothing. Every entry is normalised
    to end in ``/`` so ``nomos/data`` cannot claim ``nomos/data-sources/``.
    An absolute path or a ``.``/``..`` segment would exempt the whole tree,
    so it is refused rather than honoured — a misdeclared root fails the job
    loudly instead of silently widening the exemption.
    """
    extra: list[str] = []
    for raw in os.environ.get(EXEMPT_PATHS_ENV, "").split(","):
        entry = raw.strip()
        if not entry:
            continue
        segments = entry.split("/")
        if entry.startswith("/") or any(segment in (".", "..") for segment in segments):
            raise ValueError(
                f"{EXEMPT_PATHS_ENV} entry {entry!r} is not a relative corpus "
                "root inside the repository; refusing to exempt beyond it"
            )
        extra.append(entry.rstrip("/") + "/")
    return SKILL_PATH_PREFIXES + tuple(extra)


def exempt_paths_declared_since(github: GitHubApi) -> datetime | None:
    """The instant this repository's declared roots took effect; ``None`` if none.

    The environment carries the roots but not their date.  ``REVIEW_LOOP_
    EXEMPT_PATHS_SINCE`` supplies it when a caller has already resolved the
    declaration (the offline backfill); otherwise the variable's own
    ``updated_at`` is read — it moves on every edit, which errs toward dating
    older closures before the declaration, the direction that hides nothing.
    A declaration that cannot be dated raises: a terminal leg that guessed
    the date would file a never-reviewed closure as exempt in silence.
    """
    if not os.environ.get(EXEMPT_PATHS_ENV, "").strip():
        return None
    stated = os.environ.get(EXEMPT_PATHS_SINCE_ENV, "").strip()
    if stated:
        return parse_github_time(stated)
    variable = github.get(f"actions/variables/{EXEMPT_PATHS_ENV}")
    if not isinstance(variable, Mapping):
        raise TypeError(
            f"GET actions/variables/{EXEMPT_PATHS_ENV} returned no variable"
        )
    stamp = str(variable.get("updated_at") or variable.get("created_at") or "")
    if not stamp:
        raise RuntimeError(f"{EXEMPT_PATHS_ENV} variable carries no updated_at")
    return parse_github_time(stamp)


def loop_exempt_pr(github: GitHubApi, pr_number: int, *, closed_at: str = "") -> bool:
    """True when every file this PR touches sits under a loop-exempt root.

    Renames contribute both names: a file moved out of (or into) a corpus
    makes the PR mixed, and a mixed PR rides the review loop like any other.
    An empty file list is not an exempt PR — exemption is never inferred from
    absence, and neither is it inferred from an incomplete list: the files
    endpoint stops at 3,000 entries and ``paginate`` reads that short final
    page as the whole diff, so a >3,000-file PR whose first 3,000 paths all
    sit under a corpus root would otherwise skip summon, burn, exhaustion and
    the belt's terminal telemetry with nothing else gating it.  The listed
    count is therefore checked against the PR object's ``changed_files``
    before exemption is granted, and a short list fails closed.

    ``closed_at`` dates the question: a closed PR is judged under the roots in
    force when it closed, so a corpus declared after the closure does not
    reach back and exempt a PR the belt routed for review.  The routing paths
    ask about open PRs and pass nothing — today's declaration is the one in
    force.
    """
    prefixes = loop_exempt_prefixes()
    if closed_at and len(prefixes) > len(SKILL_PATH_PREFIXES):
        since = exempt_paths_declared_since(github)
        if since is not None and parse_github_time(closed_at) < since:
            prefixes = SKILL_PATH_PREFIXES
    paths: list[str] = []
    listed = 0
    for entry in github.paginate(f"pulls/{pr_number}/files"):
        listed += 1
        for key in ("filename", "previous_filename"):
            value = entry.get(key)
            if value:
                paths.append(str(value))
    if not paths or not all(path.startswith(prefixes) for path in paths):
        return False
    return pr_files_are_complete(github, pr_number, listed)


def pr_files_are_complete(github: GitHubApi, pr_number: int, listed: int) -> bool:
    """True when ``listed`` file entries are the PR's whole diff.

    Asked only where a short list would grant something — exemption is the
    load-bearing side, so it is the side that must be proven — which is also
    why the extra read is not paid on the PRs that ride the loop anyway.
    One entry is one file (a rename is a single entry carrying two names),
    so the count compares against ``changed_files`` on the PR object, which
    is not capped the way the files listing is.  A PR object without an
    integer ``changed_files`` is a broken read, not a complete list: it
    raises rather than answering, because both answers would be a guess.
    """
    detail = github.get(f"pulls/{pr_number}")
    if not isinstance(detail, Mapping):
        raise TypeError(f"GET pulls/{pr_number} did not return an object")
    changed = detail.get("changed_files")
    if not isinstance(changed, int) or isinstance(changed, bool):
        raise TypeError(
            f"pulls/{pr_number} carries no integer changed_files "
            f"({changed!r}); the file list cannot be proven complete"
        )
    if listed < changed:
        print(
            f"pulls/{pr_number}/files listed {listed} of {changed} changed "
            "files — the truncated list cannot prove loop exemption"
        )
        return False
    return True


def is_quota_refusal_body(body: str) -> bool:
    """True when this text is the connector's account-wide quota refusal.

    One predicate for both channels (submitted review and issue comment).
    A refusal is not a verdict: it must not enter the result stream, must
    not route as CLEAN or findings, and must not count as a reviewed head.
    """
    return str(body or "").lstrip().startswith(CODEX_QUOTA_REFUSAL_PREFIX)


def review_findings(
    comments: Sequence[Mapping[str, Any]], review_id: int, codex_login: str
) -> list[dict[str, Any]]:
    """Select one review's inline Codex findings from the PR's comment list.

    Bind on ``pull_request_review_id``, never on ``commit_id == head``.
    GitHub repositions older unresolved comments onto the live head, so a
    ``commit_id`` filter mixes leftover rounds into the current verdict.

    The comment list is fetched once and filtered per review, so building a
    whole-PR round history costs no additional API calls.  A comment whose
    body is not as-of-closure keeps ``body_as_of_closure=False`` on the
    finding so severity is not invented from the cleared text.
    """
    findings: list[dict[str, Any]] = []
    for comment in comments:
        user = comment.get("user")
        if not isinstance(user, Mapping) or user.get("login") != codex_login:
            continue
        if comment.get("pull_request_review_id") != review_id:
            continue
        finding: dict[str, Any] = {
            "path": comment.get("path") or "?",
            "line": comment.get("line") or comment.get("original_line") or "?",
            "body": str(comment.get("body") or ""),
        }
        # A post-closure edit clears the body.  Keep the marker so
        # ``severity_counts`` does not invent P3 from the empty string.
        if comment.get(BODY_AS_OF_CLOSURE) is False:
            finding[BODY_AS_OF_CLOSURE] = False
        findings.append(finding)
    return findings


def codex_review_heads(
    reviews: Sequence[Mapping[str, Any]], codex_login: str
) -> list[str]:
    """Return distinct reviewed commit ids in review order."""
    heads: list[str] = []
    for review in reviews:
        user = review.get("user")
        if not isinstance(user, Mapping) or user.get("login") != codex_login:
            continue
        if is_quota_refusal_body(str(review.get("body") or "")):
            continue
        head_sha = str(review.get("commit_id") or "").strip()
        if head_sha and head_sha not in heads:
            heads.append(head_sha)
    return heads


# The clean-verdict predicate, vendored byte-identical from
# ``skills/code-review/scripts/src/weave_reviewkit/verdicts.py``.  This helper is
# standard-library-only by law and is copied into adopters that never receive the
# skill's package, so it cannot import the module -- and two independent readings
# of the same Codex prose is the drift KRA-1222 closes.  Edit the module; the
# gate ``test_the_vendored_verdict_predicate_is_byte_identical`` stays red until
# this region matches it exactly.
# --- BEGIN weave-review-loop:verdict-predicate ---
# No formatter owns this region, in either home.  These are vendored bytes and
# the two homes sit under different ruff line-length settings (88 at the
# weave-doctrine root, 100 in this package), so any construct whose joined form
# lands between the two widths would be split in one copy and joined in the
# other, and byte identity would be unreachable.  Hand-formatted to 88.
# fmt: off
# The review connector's clean comment opens with this exact sentence and
# declares its head in a ``**Reviewed commit:**`` footer.
CODEX_CLEAN_COMMENT_PREFIX = "Codex Review: Didn't find any major issues."
# A verdict heading, either spelling.  ``## Review Result`` is the shape the
# task channel emitted through 2026-08; ``## Review verdict`` is the shape
# observed on sokrates#1113, where two of them classified as ``unknown``, left
# no marker on the PR, and let the scheduled leg nudge for a review that had
# already been given -- two of seven bounded rounds spent re-asking an answered
# question (KRA-1222).  The noun is matched case-insensitively; ``Review`` is
# required, so a bare ``## Verdict`` is still not a verdict heading and
# arbitrary chatter cannot be promoted by its heading alone.
CODEX_VERDICT_HEADING_RE = re.compile(
    r"^##[ \t]+Review[ \t]+(?:Result|verdict)\b", re.IGNORECASE
)
CODEX_RESULT_CLEAN_PHRASE = "no blocking findings"
# The terse clean sentence the reviewkit's own lineage reader has always
# accepted.  It is carried forward here so collapsing the copies loses no
# coverage -- but as a whole opening sentence now, never as a substring.
CODEX_TERSE_CLEAN_PHRASE = "no findings"
# The clean sentence that carries its own head.  The SHA is part of the
# assertion, so a verdict in this shape is an exact-head claim by construction
# and ``task_verdict_clean_head`` binds it exactly as ``**Reviewed commit:**``
# binds the other channel.  Backticks are optional: the peel below removes
# emphasis and terminators but not code fencing.
CODEX_EXACT_HEAD_CLEAN_RE = re.compile(
    r"^no major issues found at exact head `?([0-9a-f]{40})`?$"
)
# The footer the review connector declares its reviewed head in.  The digits
# are however many GitHub chose to display, so this yields a commit-ish and
# never a head: expanding it is the caller's job, against whatever authority
# the caller has.
REVIEWED_COMMIT_PATTERN = re.compile(
    r"\*\*Reviewed commit:\*\*\s*`([0-9a-fA-F]{7,40})`"
)
# Codex anchors every claim in a task-channel verdict to a file permalink at the
# exact tree it read.  ``commit``/``pull`` links are deliberately excluded: they
# reference a commit under discussion, not the tree the verdict was formed on.
PERMALINK_COMMIT_PATTERN = re.compile(
    r"https://github\.com/([A-Za-z0-9._-]+/[A-Za-z0-9._-]+)"
    r"/(?:blob|blame)/([0-9a-fA-F]{40})/"
)
# A lone period or bang ends a sentence.  Ellipsis is continuation -- the
# prefix check `tail[0] in ".!"` treated the first dot of "..." as a stop.
_SENTENCE_END = re.compile(r"(?<!\.)\.(?!\.)|!")


def _opening_sentence(statement: str) -> str:
    """First sentence of a verdict line.

    Ellipsis (``...`` / ``…``) continues the sentence; a lone ``.`` or ``!``
    ends it.  Keying on this boundary -- not on a prefix of the line -- is what
    keeps ``No blocking findings... yet`` from counting as a clean verdict.
    """
    normalized = statement.replace("…", "...")
    match = _SENTENCE_END.search(normalized)
    if match is None:
        return normalized
    return normalized[: match.end()]


def _asserted_sentence(statement: str) -> str:
    """The opening sentence with emphasis and its terminator peeled off.

    Closing emphasis markers and a real terminator may arrive in either order
    (``**phrase**.`` vs ``**phrase.**``); peel both until stable.  Ellipsis is
    continuation, never a stop, so it is never stripped -- a line that reduces
    to the clean phrase only because its trailing dots were removed is a
    withheld verdict, not a clean one.
    """
    opening = _opening_sentence(statement)
    has_stop = _SENTENCE_END.search(opening) is not None
    asserted = opening
    while True:
        nxt = asserted.rstrip("*_ ").strip()
        if has_stop and not nxt.endswith("..."):
            nxt = nxt.rstrip(".! ").strip()
        if nxt == asserted:
            return asserted
        asserted = nxt


def _verdict_statement(body: str) -> str | None:
    """The verdict sentence beneath a verdict heading, lowered and unadorned.

    ``None`` when the body does not open with a verdict heading at all; ``""``
    when it does but says nothing under it.

    The verdict is the first sentence on a line of its *own* beneath the
    heading.  Text trailing the heading on the same line is heading, not
    verdict: ``weave_reviewkit.report`` writes
    ``## Review verdict — `initial` generation 2``, and reading that suffix as
    the verdict would classify a substitute's report by its own metadata.
    """
    heading = CODEX_VERDICT_HEADING_RE.match(body)
    if heading is None:
        return None
    _, _, remainder = body[heading.end() :].partition("\n")
    for line in remainder.splitlines():
        statement = line.strip().lstrip("*_->#").strip().lower()
        if statement:
            return statement
    return ""


def task_verdict_is_clean(body: str) -> bool:
    """True only when the opening *sentence* under the heading is clean.

    The verdict is the first sentence, not a prefix of it.  ``No blocking
    findings could be ruled out.`` and ``No blocking findings... yet`` share
    the clean phrase as an opening but are different sentences; treating either
    as CLEAN would hand merge authority to a verdict Codex withheld.
    """
    statement = _verdict_statement(body)
    if not statement:
        return False
    asserted = _asserted_sentence(statement)
    if asserted in (CODEX_RESULT_CLEAN_PHRASE, CODEX_TERSE_CLEAN_PHRASE):
        return True
    return CODEX_EXACT_HEAD_CLEAN_RE.match(asserted) is not None


def task_verdict_clean_head(body: str) -> str | None:
    """The exact head a clean verdict names inside its own assertion.

    Only the ``No major issues found at exact head `<40-hex>`.`` shape names
    one.  Every other clean shape returns ``None`` and the caller falls back to
    the head the body declares or pins some other way -- an absent SHA here is
    "this sentence made no head claim", never "this verdict covers any head".
    """
    statement = _verdict_statement(body)
    if not statement:
        return None
    match = CODEX_EXACT_HEAD_CLEAN_RE.match(_asserted_sentence(statement))
    return match.group(1) if match else None


def permalink_commit(body: str, repository: str) -> str | None:
    """Return the one commit this body's own-repository permalinks all pin.

    Two distinct SHAs mean the comment spans trees, so no single reviewed head
    can be claimed.  Links into other repositories are ignored outright -- a SHA
    from elsewhere is not evidence about this pull request.
    """
    shas = {
        match.group(2).lower()
        for match in PERMALINK_COMMIT_PATTERN.finditer(body)
        if match.group(1).lower() == repository.lower()
    }
    if len(shas) != 1:
        return None
    return shas.pop()


def clean_verdict_commitish(body: str, repository: str) -> str | None:
    """The commit a clean Codex verdict names, in whichever shape names it.

    Three shapes carry a head and the order between them is a precedence, not a
    fallback chain of equals: where Codex writes ``No major issues found at
    exact head `<sha>`.`` the SHA *is* the claim, ``**Reviewed commit:**`` is a
    footer the connector appends, and a permalink is the tree one individual
    citation was read at.

    ``None`` is "this verdict established no head".  Every consumer of a clean
    verdict must fail closed on it -- the belt refuses closure, the lineage
    reader refuses the CLEAN classification -- because a clean sentence about no
    particular tree is not a clean sentence about this one.  Reading only the
    exact-head shape here left every connector clean comment unbound, and the
    reviewkit published them as CLEAN anyway with no head at all.

    The result may be abbreviated: only ``REVIEWED_COMMIT_PATTERN`` can match a
    short commit-ish, and expanding it needs an authority this module does not
    have.  The caller expands it -- the belt against the repository, the lineage
    reader against the heads the PR's own thread establishes.
    """
    stripped = body.lstrip()
    asserted = task_verdict_clean_head(stripped)
    if asserted:
        return asserted
    match = REVIEWED_COMMIT_PATTERN.search(body)
    if match:
        return match.group(1).lower()
    return permalink_commit(body, repository)


def codex_comment_is_clean(body: str) -> bool:
    """True when a Codex-authored body asserts a clean review, either channel.

    The single predicate both consumers ask.  Authorship is the caller's
    business: this says only what the prose asserts.
    """
    stripped = body.lstrip()
    if stripped.startswith(CODEX_CLEAN_COMMENT_PREFIX):
        return True
    return task_verdict_is_clean(stripped)


def clean_verdict_binds_head(body: str, head_sha: str) -> bool:
    """True when this body asserts a clean verdict *for* ``head_sha``.

    Clean-ness and binding are one question at every consumer -- the belt
    routes a wake on it, classifies a result event by it and reports history
    from it, and the reviewkit writes a lineage row from it -- so the two
    halves live here together instead of being re-paired at each call site.

    A body whose exact-head sentence names a different SHA is a clean verdict
    about another tree and binds nothing here: fail closed.  ``None`` from
    ``task_verdict_clean_head`` is "this sentence made no head claim", so the
    caller's own verified head stands -- the connector's clean comment and the
    terse task verdict both take that path.
    """
    stripped = body.lstrip()
    if not codex_comment_is_clean(stripped):
        return False
    asserted = task_verdict_clean_head(stripped)
    return asserted is None or asserted == head_sha.lower()


# A severity badge is ``P<level>-<colour>``.  The level is the contract; the
# colour is the emitting reviewer's rendering choice, so it is not matched --
# pinning ``P1-orange`` and ``P2-yellow`` made every other level unreadable,
# and an unreadable level fell through to the LOWEST bucket.
SEVERITY_BADGE = re.compile(r"\bP([0-3])-[A-Za-z]+\b")


def finding_severity(body: str) -> int:
    """The level a finding's own body declares, folded to ``1``, ``2`` or ``3``.

    Codex writes the badge in the inline comment, not in the review summary,
    so this is the only place either consumer can learn what a round found.
    P0 folds into P1, the same fold the review integration applies to its own
    legacy three-bucket marker (``weave_reviewkit.report``); without it a
    catastrophic finding is published in the P3 bucket and reads as a nit.  A
    body carrying no badge is a finding too and takes P3: the belt counts it,
    so the history that reports the same round must count it as well.
    """
    badge = SEVERITY_BADGE.search(body)
    level = int(badge.group(1)) if badge else 3
    return max(1, level)


# fmt: on
# --- END weave-review-loop:verdict-predicate ---


def severity_counts(findings: Sequence[Mapping[str, Any]]) -> dict[str, int]:
    counts = {"p1": 0, "p2": 0, "p3": 0, "total": len(findings)}
    for finding in findings:
        # ``finding_severity`` is the vendored region's, not this file's: the
        # history packet reports the counts this wake publishes, so a badge
        # read two ways here is the KRA-1222 drift rebuilt in the severity
        # column.  P0 folds into P1 and an unbadged comment takes P3 there.
        # An untrusted (post-closure-edited) body is not unbadged: the original
        # level is gone, and the empty string must not become P3.
        if finding.get(BODY_AS_OF_CLOSURE) is False:
            continue
        level = finding_severity(str(finding.get("body") or ""))
        counts[f"p{level}"] += 1
    return counts


def codex_comment_kind(body: str) -> str:
    """Classify one Codex-authored PR comment into the loop's result vocabulary.

    Codex speaks through two channels.  The review connector emits
    ``CODEX_CLEAN_COMMENT_PREFIX`` with a declared ``**Reviewed commit:**``.  A
    Codex *task* asked to review the PR emits a verdict heading -- ``## Review
    Result`` or ``## Review verdict`` -- and anchors its claims in file
    permalinks, or names its head inside the verdict sentence itself.  Both are
    verdicts.

    A task-channel verdict that is not affirmatively clean is ``task-verdict``:
    findings delivered that way reach neither ``route_review`` nor the burn
    twin, so the loop has no route for them and must say so.

    A task that *changed* code reports under ``### Summary``; that is a work
    report, never a verdict — its permalinks point at the tree the task read
    before committing on top of it, so its head is stale by construction.

    Everything else is ``unknown`` on purpose: an unrecognised shape must be
    reported, not silently dropped, which is the defect this vocabulary closes.
    """
    stripped = body.lstrip()
    if stripped.startswith(CODEX_CONNECTOR_ERROR_PREFIX):
        return CODEX_COMMENT_CONNECTOR_ERROR
    if is_quota_refusal_body(stripped):
        return CODEX_COMMENT_QUOTA_REFUSAL
    if stripped.startswith(CODEX_CLEAN_COMMENT_PREFIX):
        return CODEX_COMMENT_CLEAN
    if CODEX_VERDICT_HEADING_RE.match(stripped):
        if task_verdict_is_clean(stripped):
            return CODEX_COMMENT_CLEAN
        return CODEX_COMMENT_TASK_VERDICT
    if stripped.startswith(CODEX_TASK_REPORT_HEADING):
        return CODEX_COMMENT_TASK_REPORT
    return CODEX_COMMENT_UNKNOWN


def comment_commit_reference(body: str, repository: str) -> str | None:
    """Any commit this comment points at, whatever the comment's shape."""
    match = REVIEWED_COMMIT_PATTERN.search(body)
    if match:
        return match.group(1).lower()
    for permalink in PERMALINK_COMMIT_PATTERN.finditer(body):
        if permalink.group(1).lower() == repository.lower():
            return permalink.group(2).lower()
    return None


def clean_comment_commitish(
    comment: Mapping[str, Any], codex_login: str, repository: str
) -> str | None:
    """Extract the reviewed commit from a Codex clean verdict in either format."""
    user = comment.get("user")
    if not isinstance(user, Mapping) or user.get("login") != codex_login:
        return None
    body = str(comment.get("body") or "")
    if codex_comment_kind(body) != CODEX_COMMENT_CLEAN:
        return None
    # Authorship and shape are this function's business; which head the verdict
    # names is the shared reading's, so the precedence between the three shapes
    # is stated once, in the vendored region.
    return clean_verdict_commitish(body, repository)


def clean_comment_head(
    github: GitHubApi, comment: Mapping[str, Any], codex_login: str
) -> str | None:
    """Resolve Codex's displayed short commit to one exact repository SHA."""
    commitish = clean_comment_commitish(comment, codex_login, github.repository)
    if commitish is None:
        return None
    if len(commitish) == 40:
        return commitish
    try:
        commit = github.get(f"commits/{commitish}")
    except ApiHttpError as error:
        # A stale force-pushed commit may no longer resolve. It cannot establish
        # current-head closure, but every transient or authority failure must
        # fail visibly so the workflow retries instead of consuming a round.
        if error.status_code == 404:
            return None
        raise
    if not isinstance(commit, Mapping):
        raise TypeError("GitHub commit lookup returned an invalid response")
    resolved = str(commit.get("sha") or "").lower()
    if not re.fullmatch(r"[0-9a-f]{40}", resolved):
        raise RuntimeError("GitHub commit lookup returned an invalid commit id")
    return resolved


# One entry of the result stream: ``(time, order, head, kind, source, identity)``.
# ``order`` is the event's index within ONE fetch and breaks same-second ties
# deterministically; ``identity`` is GitHub's own id for the record and is the
# only field that survives a second fetch, which is what a publication-time
# re-read has to compare (KRA-1368).
ResultEvent = tuple[datetime, int, str, str, str, str]


def result_event_identity(channel: str, record: Mapping[str, Any]) -> str:
    """Name one result event by the record GitHub published it as.

    ``review:<id>`` or ``comment:<id>``.  Time cannot name an event: GitHub's
    ``submitted_at``/``created_at`` are whole seconds, so a second verdict of
    the same kind landing in the same second is indistinguishable from the
    first by timestamp alone.  ``order`` cannot either — it is the index within
    one fetch, and appending a review shifts every comment event's index, so
    two fetches of the same PR disagree about it the moment anything lands.

    A record whose id is missing or unusable yields ``""``, which
    ``result_state_unchanged`` refuses to match against anything, including
    another ``""``.  An event the loop cannot name must never be able to
    certify that the verdict state has not moved.
    """
    raw = record.get("id")
    if isinstance(raw, bool) or not isinstance(raw, (int, str)):
        return ""
    text = str(raw).strip()
    return f"{channel}:{text}" if text else ""


def _review_id_from_event_identity(identity: str) -> int | None:
    """The review id a ``review:<id>`` result identity names, if any."""
    prefix = "review:"
    if not identity.startswith(prefix):
        return None
    try:
        return int(identity[len(prefix) :])
    except ValueError:
        return None


def _untrusted_body_without_inline_findings(
    item: Mapping[str, Any], inline_findings: Sequence[Any] | None
) -> bool:
    """True when identity is kept but the item cannot be dated as a verdict.

    A post-closure edit clears the body.  Surviving inline comments still
    classify the round; with none, the review enters the result stream as
    ``UNKNOWN_REVIEW_RESULT`` — the round was consumed, its verdict is not
    known — and must not be the history selector's latest review for the head.
    """
    return item.get(BODY_AS_OF_CLOSURE) is False and not inline_findings


def codex_result_events(
    github: GitHubApi,
    reviews: Sequence[Mapping[str, Any]],
    comments: Sequence[Mapping[str, Any]],
    codex_login: str,
    *,
    pr_number: int,
    review_comments: Sequence[Mapping[str, Any]] | None = None,
) -> list[ResultEvent]:
    """Return time-ordered results as ``(time, order, head, kind, source, identity)``.

    ``kind`` is ``clean`` for a verdict that binds this head and ``findings``
    otherwise.  Both channels are retained — including a later CLEAN on a head
    that already had findings — so a retrospective can pick the later verdict
    without treating the earlier review as current.

    A submitted review is a verdict channel like any other: Codex answers a
    summons in a review body as readily as in a comment, and ``route_review``
    wakes the author on exactly that shape.  Recording it as ``findings``
    regardless left every consumer of this stream contradicting that route —
    ``redeliver_standing_wake`` read a findings state, found no inline
    comments for it, and dropped the one-hour backstop under an unacted CLEAN,
    while ``round_history`` reported the round as a findings review with
    nothing retrievable.  The binding is ``clean_verdict_binds_head``, shared
    with that route, so a clean sentence naming another SHA is not clean here
    either.

    A review's body is not the whole verdict.  ``route_review`` computes
    ``review_findings(...)`` first and wakes the burn seat whenever it is
    non-empty, whatever the body says, so a ``No blocking findings`` summary
    submitted alongside P2/P3 inline comments is a findings review at the live
    route.  Classifying it ``clean`` from the body alone put this stream back
    in contradiction with that route in the one direction that loses work:
    ``redeliver_standing_wake`` clears the standing digest and re-delivers a
    CLEAN *merge* wake, and ``round_history`` marks the round closed, for a
    head Codex had just filed findings on.  Inline findings therefore outrank
    a clean body here as they do there.  The comment list is fetched lazily —
    only a body that already binds clean can need it, which is rare — and
    ``review_comments`` lets a caller that already holds the list reuse it.  A
    review whose id cannot bind its own inline comments fails closed to
    ``findings``: an unverifiable clean body must never authorise a merge wake.

    ``source`` is ``codex`` or ``substitute``.  Kind alone cannot say which
    producer's result won a head: when a Codex review and a substitute marker
    both land on one head, a consumer that knows only ``findings`` reaches for
    the Codex inline comments even where the substitute verdict is the later
    one, and reports the superseded severities.  The producer travels with the
    event so the winner can be selected rather than guessed.

    A stale short commit can become unresolvable after history changes. It still
    consumed an automatic review round, so retain a namespaced short key for the
    bounded-loop count without ever treating it as exact-head closure.

    Finding-reviews and clean comments are independent channels. Listing one
    channel then the other is not chronological, so a retrospective would number
    a later findings head before an earlier CLEAN. Merge by timestamp before
    treating the list as round order.
    """
    events: list[ResultEvent] = []
    inline_comments = review_comments

    def inline_findings_for(review: Mapping[str, Any]) -> list[dict[str, Any]] | None:
        """Matching inline findings, or ``None`` when the review id cannot bind."""
        nonlocal inline_comments
        try:
            review_id = int(review["id"])
        except (KeyError, TypeError, ValueError):
            return None
        if inline_comments is None:
            inline_comments = github.paginate(f"pulls/{pr_number}/comments")
        return review_findings(inline_comments, review_id, codex_login)

    def review_kind(review: Mapping[str, Any], body: str, head_sha: str) -> str:
        if not clean_verdict_binds_head(body, head_sha):
            return "findings"
        findings = inline_findings_for(review)
        if findings:
            return "findings"
        if findings is None:
            return "findings"
        return "clean"

    for review in reviews:
        user = review.get("user")
        if not isinstance(user, Mapping) or user.get("login") != codex_login:
            continue
        if is_quota_refusal_body(str(review.get("body") or "")):
            continue
        head_sha = str(review.get("commit_id") or "").strip()
        if not head_sha:
            continue
        body = str(review.get("body") or "")
        if review.get(BODY_AS_OF_CLOSURE) is False:
            # Summary text is a post-closure edit.  Classify from pre-closure
            # inline comments; with none, the review cannot be dated as a
            # verdict — but its id, head and submission time still prove the
            # round, so it is kept as a non-closing unknown result rather than
            # dropped, and never read as CLEAN or as a findings round.
            inlines = inline_findings_for(review)
            if _untrusted_body_without_inline_findings(review, inlines):
                kind = UNKNOWN_REVIEW_RESULT
            else:
                kind = "findings"
        else:
            kind = review_kind(review, body, head_sha)
        events.append(
            (
                result_event_time(review.get("submitted_at")),
                len(events),
                head_sha,
                kind,
                "codex",
                result_event_identity("review", review),
            )
        )
    for comment in comments:
        commitish = clean_comment_commitish(comment, codex_login, github.repository)
        if commitish is None:
            continue
        resolved = clean_comment_head(github, comment, codex_login)
        result_head = resolved or f"{UNRESOLVED_CLEAN_PREFIX}{commitish}"
        events.append(
            (
                result_event_time(comment.get("created_at")),
                len(events),
                result_head,
                "clean",
                "codex",
                result_event_identity("comment", comment),
            )
        )
    for comment, verdict in substitute_verdicts(comments):
        events.append(
            (
                verdict["at"],
                len(events),
                verdict["head"],
                verdict["kind"],
                "substitute",
                result_event_identity("comment", comment),
            )
        )
    events.sort()
    return events


def substitute_verdict_marker_state(comments: Sequence[Mapping[str, Any]]) -> str:
    """``present``, ``malformed`` or ``absent``: does any comment carry a
    substitute verdict marker, trust aside?

    Trust is not read here: a forged marker is ``present`` and is refused,
    loudly, by ``route_substitute_verdict``.  ``malformed`` is a body that
    names the family without a marker that parses — the shape a substitute
    who mistyped the grammar posts.  A summon comment quotes the grammar
    and is excluded by its own marker, so it is ``absent``.
    """
    state = "absent"
    for comment in comments:
        body = str(comment.get("body") or "")
        if SUBSTITUTE_VERDICT_MARKER_RE.search(body):
            return "present"
        if (
            SUBSTITUTE_VERDICT_MARKER_PREFIX.removeprefix("<!-- ") in body
            and SUBSTITUTE_SUMMON_MARKER_PREFIX not in body
        ):
            state = "malformed"
    return state


def substitute_verdicts(
    comments: Sequence[Mapping[str, Any]],
) -> list[tuple[Mapping[str, Any], dict[str, Any]]]:
    """Trusted substitute exact-head verdicts, as ``(comment, parsed)`` pairs.

    A substitute verdict is a PR comment by a trusted control identity carrying
    the ``substitute-verdict`` marker.  The marker is the whole contract — full
    head SHA, the substitute actor, and ``clean`` or ``findings:p1:p2:p3`` —
    because seats' verdict prose drifts and the loop must never parse it.  An
    untrusted author's marker is a forgery and never counts, same trust rule as
    every other control marker.
    """
    trusted = trusted_control_logins()
    verdicts: list[tuple[Mapping[str, Any], dict[str, Any]]] = []
    for comment in comments:
        user = comment.get("user")
        if not isinstance(user, Mapping) or user.get("login") not in trusted:
            continue
        match = SUBSTITUTE_VERDICT_MARKER_RE.search(str(comment.get("body") or ""))
        if match is None:
            continue
        counts = {"p1": 0, "p2": 0, "p3": 0}
        if match.group(3) != "clean":
            # The marker, not the prose, is the machine contract — severity
            # counts parse from it deterministically.
            _, p1, p2, p3 = match.group(3).split(":")
            counts = {"p1": int(p1), "p2": int(p2), "p3": int(p3)}
        verdicts.append(
            (
                comment,
                {
                    "at": result_event_time(comment.get("created_at")),
                    "head": match.group(1).lower(),
                    "actor": match.group(2),
                    "kind": "clean" if match.group(3) == "clean" else "findings",
                    "counts": counts,
                },
            )
        )
    return verdicts


def substitute_verdict_line(parsed: Mapping[str, Any]) -> str:
    """``<actor> clean`` or ``<actor> findings:<p1>:<p2>:<p3>`` — the line a
    merging seat reads (readiness limb 2)."""
    if parsed["kind"] == "clean":
        return f"{parsed['actor']} clean"
    counts = parsed["counts"]
    return f"{parsed['actor']} findings:{counts['p1']}:{counts['p2']}:{counts['p3']}"


def substitute_verdict_report(
    head_sha: str, comments: Sequence[Mapping[str, Any]]
) -> str:
    """The line a merging seat reads for ``head_sha``: the latest accepted
    verdict, a refusal, or nothing.

    The reader is ``substitute_verdicts`` — the belt's own grammar and trust
    rule — so this cannot accept a marker the loop refuses: the readiness
    reference used to re-spell the grammar in jq, and three review rounds each
    found that copy wider than the helper (no author filter; a loose verdict
    token).  One reader.

    A trusted comment posted AFTER the last accepted verdict that names the
    family but does not parse is the shape ``route_comment_event`` fails
    loudly as malformed: a seat tried to change the verdict and mistyped the
    marker.  The older verdict does not stand behind it — the answer is the
    refusal, until the marker is reposted verbatim.

    Reposting IS the remedy, so the malformed comment cannot be the end of the
    read: the whole list is walked, and an accepted verdict for this head that
    lands after a malformed attempt supersedes it.  The refusal is the answer
    only when the LAST trusted marker-shaped comment for this head is the
    malformed one — otherwise a seat that corrected its marker would keep
    reading the refusal until it edited or deleted the mistyped comment,
    which is not what the remedy says.
    """
    head = head_sha.lower()
    trusted = trusted_control_logins()
    latest: dict[str, Any] | None = None
    refused: Mapping[str, Any] | None = None
    for comment in comments:
        user = comment.get("user")
        if not isinstance(user, Mapping) or user.get("login") not in trusted:
            continue
        accepted = [parsed for _, parsed in substitute_verdicts([comment])]
        if accepted:
            if accepted[0]["head"] == head:
                # The repost the refusal asks for: it replaces both the older
                # verdict and the malformed attempt standing between them.
                latest = accepted[0]
                refused = None
            continue
        if (
            latest is not None
            and substitute_verdict_marker_state([comment]) == "malformed"
        ):
            refused = comment
    if refused is not None:
        return (
            "MALFORMED SUBSTITUTE VERDICT after the last accepted one "
            f"(comment {refused.get('id', '?')}); the marker must be reposted "
            "verbatim before this head has a verdict"
        )
    return substitute_verdict_line(latest) if latest is not None else ""


def report_substitute_verdict(head_sha: str, pages: Any, out: Any) -> None:
    """Print ``substitute_verdict_report`` for the comment pages on stdin.

    ``pages`` is what ``gh api …/comments --paginate --slurp`` emits (a list
    of pages) or a flat list of comments.
    """
    comments = [
        comment
        for page in pages
        for comment in (page if isinstance(page, list) else [page])
    ]
    line = substitute_verdict_report(head_sha, comments)
    if line:
        print(line, file=out)


def standing_substitute_findings(
    comments: Sequence[Mapping[str, Any]], head_sha: str
) -> tuple[Mapping[str, Any], dict[str, Any]] | None:
    """The latest substitute FINDINGS verdict for this head, with its comment.

    The comment body IS the digest — the marker contract requires the
    substitute to carry the findings in the verdict comment itself, and the
    loop never re-parses seat prose into structure.
    """
    latest: tuple[Mapping[str, Any], dict[str, Any]] | None = None
    for comment, verdict in substitute_verdicts(comments):
        if verdict["head"] != head_sha.lower() or verdict["kind"] != "findings":
            continue
        if latest is None or verdict["at"] > latest[1]["at"]:
            latest = (comment, verdict)
    return latest


def result_heads_from_events(
    events: Sequence[ResultEvent],
) -> list[str]:
    """Distinct heads in first-seen time order; a later event does not add a round."""
    heads: list[str] = []
    for _, _, head, _, _, _ in events:
        if head not in heads:
            heads.append(head)
    return heads


def latest_result_by_head(
    events: Sequence[ResultEvent],
) -> dict[str, dict[str, Any]]:
    """The result that won each head: its ``kind``, ``source``, time and identity.

    Latest-wins across both channels and both producers.  The winner's SOURCE
    is carried out with its kind, because that is what decides where the head's
    counts and digest may be read from — a Codex review's inline comments or a
    substitute marker's own verdict comment.  A consumer handed the kind alone
    has to infer the producer from whichever record happens to exist, which
    picks the superseded one whenever both do.

    The winner's IDENTITY travels with it for a different consumer: a
    publication computed from one read of this map has to prove, immediately
    before it posts, that a second read still names the same event.  Kind and
    time cannot carry that proof on their own — GitHub stamps whole seconds, so
    a newer verdict of the same kind in the same second is invisible to both
    (KRA-1368).

    An ``UNKNOWN_REVIEW_RESULT`` wins a head only when nothing else does: its
    verdict is unrecoverable, so it cannot supersede a known result on the
    same head, and a known result supersedes it whenever it lands.
    """
    latest: dict[str, tuple[datetime, int, str, str, str]] = {}
    for at, order, head, kind, source, identity in events:
        previous = latest.get(head)
        if previous is None:
            latest[head] = (at, order, kind, source, identity)
            continue
        unknown = kind == UNKNOWN_REVIEW_RESULT
        previous_unknown = previous[2] == UNKNOWN_REVIEW_RESULT
        if unknown and not previous_unknown:
            continue
        if (previous_unknown and not unknown) or (at, order) >= (
            previous[0],
            previous[1],
        ):
            latest[head] = (at, order, kind, source, identity)
    return {
        head: {"kind": kind, "source": source, "at": at, "identity": identity}
        for head, (at, _order, kind, source, identity) in latest.items()
    }


def codex_result_heads(
    github: GitHubApi,
    reviews: Sequence[Mapping[str, Any]],
    comments: Sequence[Mapping[str, Any]],
    codex_login: str,
    *,
    pr_number: int,
    review_comments: Sequence[Mapping[str, Any]] | None = None,
) -> list[str]:
    """Return distinct finding-review and clean-comment heads in time order."""
    return result_heads_from_events(
        codex_result_events(
            github,
            reviews,
            comments,
            codex_login,
            pr_number=pr_number,
            review_comments=review_comments,
        )
    )


def result_round_for_head(reviewed_heads: Sequence[str], head_sha: str) -> int:
    """Return this head's one-based round within distinct Codex results."""
    heads = list(reviewed_heads)
    if head_sha not in heads:
        heads.append(head_sha)
    return len(heads)


def review_round_for_head(
    reviews: Sequence[Mapping[str, Any]], head_sha: str, codex_login: str
) -> int:
    return result_round_for_head(codex_review_heads(reviews, codex_login), head_sha)


def _substitute_history_by_head(
    issue_comments: Sequence[Mapping[str, Any]] | None,
) -> dict[str, dict[str, Any]]:
    """Latest trusted substitute verdict per head, with its comment body.

    The marker is the machine contract (kind + counts). The comment body is
    retained as the digest so a retrospective can see earlier substitute
    rounds; seat prose is never re-parsed into structured findings.
    """
    latest: dict[str, dict[str, Any]] = {}
    if not issue_comments:
        return latest
    for comment, verdict in substitute_verdicts(issue_comments):
        head = str(verdict["head"])
        previous = latest.get(head)
        if previous is None or verdict["at"] > previous["at"]:
            counts = dict(verdict["counts"])
            latest[head] = {
                "at": verdict["at"],
                "actor": verdict["actor"],
                "kind": verdict["kind"],
                "counts": {
                    "p1": int(counts.get("p1", 0)),
                    "p2": int(counts.get("p2", 0)),
                    "p3": int(counts.get("p3", 0)),
                },
                "body": str(comment.get("body") or ""),
            }
            latest[head]["counts"]["total"] = (
                latest[head]["counts"]["p1"]
                + latest[head]["counts"]["p2"]
                + latest[head]["counts"]["p3"]
            )
    return latest


def round_history(
    reviewed_heads: Sequence[str],
    reviews: Sequence[Mapping[str, Any]],
    review_comments: Sequence[Mapping[str, Any]],
    codex_login: str,
    *,
    latest_results: Mapping[str, Mapping[str, Any]] | None = None,
    head_bases: Mapping[str, str] | None = None,
    issue_comments: Sequence[Mapping[str, Any]] | None = None,
) -> list[dict[str, Any]]:
    """Describe every consumed round in round order: head, verdict, findings.

    A retrospective needs the shape of the whole sequence, so this covers the
    same head set the bounded round count is drawn from — clean-comment rounds
    included.  A round whose inline comments are not retrievable is never
    reported as CLEAN: only a Codex clean comment establishes that, and an
    absence establishes nothing.  When a later clean comment supersedes an
    earlier findings review on the same unchanged head, the later CLEAN is
    the verdict.  Reviews are deduplicated by id because the submitted review
    under routing is also present in the paginated list.  Only the latest
    findings review per head that entered the result stream supplies the
    digest: an earlier review's comments on the same unchanged head are
    superseded by the later review's own complete assessment (an intervening
    CLEAN may have resolved them), so merging rounds would hand Theoros
    findings that are no longer live.  A post-closure-edited summary with no
    surviving inlines is not a digest candidate; when ``latest_results`` names
    the winning Codex review, that identity is the digest, not a second
    latest-per-head scan.  Where such a review is the only result on its head,
    the round is reported as consumed with an unknown verdict: never CLEAN,
    never closing, no findings invented.

    Each head's verdict is read from the producer that actually won it, not
    from whichever record exists.  A head can carry both a Codex review and a
    substitute marker; when the substitute is later, its counts and its digest
    are the round's, and the Codex inline comments it superseded are not.
    """
    latest_review_by_head: dict[str, tuple[datetime, int, int]] = {}
    seen_reviews: set[int] = set()
    for review in reviews:
        user = review.get("user")
        if not isinstance(user, Mapping) or user.get("login") != codex_login:
            continue
        if is_quota_refusal_body(str(review.get("body") or "")):
            continue
        head = str(review.get("commit_id") or "").strip()
        review_id = review.get("id")
        if not head or review_id is None or int(review_id) in seen_reviews:
            continue
        seen_reviews.add(int(review_id))
        inlines = review_findings(review_comments, int(review_id), codex_login)
        if _untrusted_body_without_inline_findings(review, inlines):
            continue
        candidate = (
            result_event_time(review.get("submitted_at")),
            len(seen_reviews),
            int(review_id),
        )
        previous = latest_review_by_head.get(head)
        if previous is None or candidate[:2] >= previous[:2]:
            latest_review_by_head[head] = candidate
    findings_by_head: dict[str, list[dict[str, Any]]] = {
        head: review_findings(review_comments, review_id, codex_login)
        for head, (_, _, review_id) in latest_review_by_head.items()
    }
    latest_result = dict(latest_results or {})
    # The event stream already chose the review.  Re-selecting latest-per-head
    # from the unfiltered list lets an omitted review shadow the winner.
    for head, winner in latest_result.items():
        if winner.get("source") != "codex":
            continue
        named = _review_id_from_event_identity(str(winner.get("identity") or ""))
        if named is None:
            continue
        findings_by_head[head] = review_findings(review_comments, named, codex_login)
    bases = dict(head_bases or {})
    substitute_by_head = _substitute_history_by_head(issue_comments)
    history: list[dict[str, Any]] = []
    for index, head in enumerate(reviewed_heads, start=1):
        findings = list(findings_by_head.get(head, []))
        winner = latest_result.get(head) or {}
        kind = winner.get("kind")
        # Which producer's result won this head. ``round_history`` may read
        # counts and a digest only from that producer's own record.
        source = winner.get("source")
        digest = ""
        # Whether this round CLOSED review, as a field rather than a prefix of
        # the rendered prose.  ``verdict`` is a human sentence and several of
        # them open with CLEAN while establishing no closure at all, so any
        # consumer that re-parses it reads the rendering instead of the result.
        closed = False
        if head.startswith(UNRESOLVED_CLEAN_PREFIX) or kind == "clean":
            substitute_round = substitute_by_head.get(str(head).lower())
            if head.startswith(UNRESOLVED_CLEAN_PREFIX):
                # The round is consumed and is reported as such, but the head
                # it reviewed could not be identified — so it is not evidence
                # that review ever closed, and no closure metric may count it.
                verdict = "CLEAN (clean comment whose commit no longer resolves)"
            elif (
                source == "substitute"
                and substitute_round is not None
                and substitute_round["kind"] == "clean"
            ):
                # A substitute CLEAN is not a Codex clean comment: the
                # retrospective compares reviewer/repair sequences, so false
                # provenance here is exactly where it misleads.  Attributed on
                # the WINNER's source: a substitute CLEAN that a later Codex
                # clean comment superseded is not the verdict of this round,
                # and naming it here would misattribute Codex's.
                verdict = f"CLEAN (substitute {substitute_round['actor']} verdict)"
                closed = True
            else:
                verdict = "CLEAN (Codex clean comment)"
                closed = True
            findings = []
            counts = severity_counts(findings)
            locations = []
        elif kind == "findings" and (
            source == "substitute" or head not in findings_by_head
        ):
            # A substitute findings verdict won this head.  It wins whether or
            # not a Codex review also exists here: an earlier Codex review the
            # substitute superseded describes a verdict that no longer stands,
            # and reading its inline comments would report the superseded
            # severities as the round's.  Where no Codex review exists at all,
            # absence from the review map is additionally NOT clean-comment
            # evidence.  The digest lives in the substitute's verdict comment;
            # the counts are in its marker and its prose is never re-parsed.
            substitute = substitute_by_head.get(str(head).lower())
            if substitute is not None:
                actor = substitute["actor"]
                verdict = (
                    f"findings verdict (substitute {actor}; "
                    "digest in the verdict comment)"
                )
                counts = dict(substitute["counts"])
                digest = str(substitute["body"])
            else:
                verdict = (
                    "findings verdict (substitute marker; "
                    "digest in the verdict comment)"
                )
                counts = {"p1": 0, "p2": 0, "p3": 0, "total": 0}
            locations = []
        elif kind == UNKNOWN_REVIEW_RESULT:
            verdict = (
                "review submitted, summary edited after closure "
                "(verdict unknown; not evidence of CLEAN)"
            )
            counts = severity_counts([])
            locations = []
        elif head not in findings_by_head:
            verdict = "CLEAN (Codex clean comment)"
            closed = True
            counts = severity_counts([])
            locations = []
        elif findings:
            verdict = "findings review"
            counts = severity_counts(findings)
            locations = [history_location(finding) for finding in findings]
        else:
            verdict = (
                "findings review submitted, 0 inline comments retrievable "
                "(not evidence of CLEAN)"
            )
            counts = severity_counts(findings)
            locations = []
        history.append(
            {
                "round": index,
                "rounds": len(reviewed_heads),
                "head": head,
                "verdict": verdict,
                "closed_review": closed,
                "counts": counts,
                "locations": locations,
                "base": bases.get(head),
                "digest": digest,
            }
        )
    return history


def finding_identity(body: str, *, max_len: int = FINDING_IDENTITY_MAX) -> str:
    """First significant line of a finding: badges and severity tags stripped.

    Path equality is not identity. The burn wake must carry this so three
    unrelated findings in one file are not treated as the same gate.
    """
    if max_len < 1:
        raise ValueError("max_len must be at least 1")
    for raw in str(body).splitlines():
        line = _IDENTITY_NOISE.sub("", raw)
        line = re.sub(r"\s+", " ", line).strip(" \t-*#_")
        if not line:
            continue
        if len(line) > max_len:
            return f"{line[: max_len - 1]}…"
        return line
    return ""


def history_location(finding: Mapping[str, Any]) -> str:
    """A wake history item: path:line, plus identity when one can be read."""
    site = f"{finding.get('path', '?')}:{finding.get('line', '?')}"
    identity = finding_identity(str(finding.get("body") or ""))
    if not identity:
        return site
    return f"{site}{LOCATION_IDENTITY_SEPARATOR}{identity}"


def location_site(location: str) -> str:
    """The ``path:line`` half of a history location, without the identity.

    ``history_location`` appends the finding's rendered title when one can be
    read, so comparing whole history items across rounds asks whether Codex
    reworded the finding — never whether the same site came back.  Recurrence
    is a question about the site, and one reworded title must not answer it
    "no".  The line stays in: a repair that moves the line is drift, which is
    what the coarser per-file grain exists to catch.
    """
    return location.split(LOCATION_IDENTITY_SEPARATOR, 1)[0]


def exhaustion_marker(head_sha: str) -> str:
    """The versioned writer form; policy-bearing (records the round bound)."""
    return (
        f"{EXHAUSTED_MARKER_PREFIX}{MARKER_SCHEMA_VERSION}:{head_sha}"
        f":max-rounds={MAX_REVIEW_ROUNDS} -->"
    )


def exhaustion_marker_state(
    comments: Sequence[Mapping[str, Any]], head_sha: str
) -> str:
    """``terminal``, ``stale-policy``, or ``absent`` for this head's gate.

    A v2 marker whose recorded ``max-rounds`` equals the current policy is
    terminal.  A v2 marker under a *different* policy is not: the situation it
    gated no longer exists, so automation may re-evaluate (and re-post a gate
    under the current policy).  A legacy unversioned marker is honored as
    terminal — its head was deliberately stopped, and "silence means stop
    safely" is load-bearing — but honoring it is logged so the estate can see
    how many pre-versioning gates still govern.
    """
    trusted = trusted_control_logins()
    state = "absent"
    for comment in comments:
        user = comment.get("user")
        if not isinstance(user, Mapping) or user.get("login") not in trusted:
            continue
        for match in EXHAUSTED_MARKER_RE.finditer(str(comment.get("body") or "")):
            v2_head, v2_rounds, legacy_head = match.groups()
            if v2_head == head_sha and v2_rounds is not None:
                if int(v2_rounds) == MAX_REVIEW_ROUNDS:
                    return "terminal"
                state = "stale-policy"
            elif legacy_head == head_sha:
                print(
                    "legacy unversioned exhaustion marker honored for head "
                    f"{head_sha} (no recorded policy; treating as terminal)"
                )
                return "terminal"
    return state


def exhaustion_gate_recorded(comments: Sequence[Mapping[str, Any]]) -> bool:
    """A trusted gate was posted at some head, under any policy.

    Any version counts, the legacy unversioned form included: the question is
    whether the PR ever reached the bound, not which bound (that is
    ``exhaustion_marker_bound``).
    """
    return marker_comment_exists(comments, EXHAUSTED_MARKER_PREFIX)


def exhaustion_marker_bound(comments: Sequence[Mapping[str, Any]]) -> int | None:
    """The round bound the gate that stopped this PR was posted under.

    ``exhausted`` is historical: it says a gate was posted at some head, under
    whatever policy was in force then.  ``MAX_REVIEW_ROUNDS`` is the policy in
    force *now*.  Reading the two together as one row claims a five-round gate
    was reached under a seven-round bound whenever the policy moved in between,
    which corrupts exactly the comparison the attribute exists for.

    Only the v2 marker records the bound it gated under, and the most recently
    posted one is the gate that ended the PR.  A legacy unversioned marker
    recorded no policy, so it yields ``None`` — the bound stays unmeasured
    rather than being filled in from today's configuration.
    """
    trusted = trusted_control_logins()
    latest: tuple[str, int] | None = None
    for comment in comments:
        user = comment.get("user")
        if not isinstance(user, Mapping) or user.get("login") not in trusted:
            continue
        created_at = str(comment.get("created_at") or "")
        for match in EXHAUSTED_MARKER_RE.finditer(str(comment.get("body") or "")):
            _, v2_rounds, _ = match.groups()
            if v2_rounds is None:
                continue
            if latest is None or created_at >= latest[0]:
                latest = (created_at, int(v2_rounds))
    return latest[1] if latest else None


def retrospective_marker(head_sha: str) -> str:
    """The receipt Theoros ends his verdict comment with; the loop never writes it."""
    return f"{RETROSPECTIVE_MARKER_PREFIX}{RETROSPECTIVE_MARKER_VERSION}:{head_sha} -->"


def retrospective_delivered(
    comments: Sequence[Mapping[str, Any]], head_sha: str
) -> bool:
    """True when some comment on this PR carries a retrospective receipt for ``head_sha``.

    Any author counts (see ``RETROSPECTIVE_MARKER_PREFIX``), and an abbreviated
    head of seven hex or more counts when it prefixes the full one.  Both
    leniencies point the same way: a false "not delivered" spends a wake and
    then posts a line on the PR saying testimony is missing, which is the one
    outcome here that damages something real.
    """
    wanted = head_sha.lower()
    for comment in comments:
        for match in RETROSPECTIVE_MARKER_RE.finditer(str(comment.get("body") or "")):
            recorded = match.group(1).lower()
            if wanted.startswith(recorded):
                return True
    return False


def retrospective_wake_marker(head_sha: str) -> str:
    """Records that a retrospective was requested at this head."""
    return f"{RETROSPECTIVE_WAKE_MARKER_PREFIX}{MARKER_SCHEMA_VERSION}:{head_sha} -->"


def retrospective_wake_marker_pattern(head_sha: str) -> re.Pattern[str]:
    """The request receipt as its reader sees it: this head, any writer version."""
    return re.compile(
        re.escape(RETROSPECTIVE_WAKE_MARKER_PREFIX)
        + _RETROSPECTIVE_MARKER_VERSION_RE
        + re.escape(f"{head_sha} -->")
    )


def retrospective_requested(
    comments: Sequence[Mapping[str, Any]], head_sha: str
) -> bool:
    """True when a wake receipt for this exact head stands, dated or not."""
    return marker_comment_exists(comments, retrospective_wake_marker_pattern(head_sha))


def retrospective_requested_at(
    comments: Sequence[Mapping[str, Any]], head_sha: str
) -> datetime | None:
    """When the wake receipt for this exact head was posted, if it was and is dated."""
    return trusted_marker_time(comments, retrospective_wake_marker_pattern(head_sha))


def retrospective_wake_receipt_body(head_sha: str, actor: str) -> str:
    """The PR-visible record that testimony was asked for and is now outstanding.

    The wake itself goes to Slack, where the loop cannot read it back.  This
    comment is what makes the request observable on the evidence it concerns —
    both to the chase leg below and to a human reading the PR cold, for whom
    "retrospective pending" and "nobody was ever asked" look identical without
    it.
    """
    return (
        f"Review-loop: the exhaustion retrospective for head `{head_sha}` was "
        f"requested from `{actor}` in #hive. The verdict is expected back here "
        "as a PR comment ending with its "
        f"`{retrospective_marker('<head>').removeprefix('<!-- ').removesuffix(' -->')}`"
        " marker. It is testimony only: "
        "it gates nothing, repairs nothing and merges nothing.\n"
        f"{retrospective_wake_marker(head_sha)}"
    )


def retrospective_chase_marker(head_sha: str, attempt: int) -> str:
    return (
        f"{RETROSPECTIVE_CHASE_MARKER_PREFIX}{MARKER_SCHEMA_VERSION}:"
        f"{head_sha}:attempt={attempt} -->"
    )


def retrospective_chase_marker_pattern(head_sha: str, attempt: int) -> re.Pattern[str]:
    """One chase record as its reader sees it: this head and attempt, any version."""
    return re.compile(
        re.escape(RETROSPECTIVE_CHASE_MARKER_PREFIX)
        + _RETROSPECTIVE_MARKER_VERSION_RE
        + re.escape(f"{head_sha}:attempt={attempt} -->")
    )


def retrospective_chased_at(
    comments: Sequence[Mapping[str, Any]], head_sha: str, attempt: int
) -> datetime | None:
    """When this head's chase of this attempt number was posted, if it was and is dated."""
    return trusted_marker_time(
        comments, retrospective_chase_marker_pattern(head_sha, attempt)
    )


def retrospective_chase_attempts(
    comments: Sequence[Mapping[str, Any]], head_sha: str
) -> int:
    """How many chases this head has already spent — the highest attempt recorded.

    Highest rather than count: a duplicate marker for one attempt must not
    consume two, and the bound is on distinct attempts.
    """
    trusted = trusted_control_logins()
    highest = 0
    for comment in comments:
        user = comment.get("user")
        if not isinstance(user, Mapping) or user.get("login") not in trusted:
            continue
        for match in RETROSPECTIVE_CHASE_MARKER_RE.finditer(
            str(comment.get("body") or "")
        ):
            if match.group(1) == head_sha:
                highest = max(highest, int(match.group(2)))
    return highest


def head_disposition_pattern(kind: str, head_sha: str) -> re.Pattern[str]:
    """Any vintage of one head-disposition marker for this exact head.

    Two forms are accepted and neither is optional.  The unversioned one is
    what the talos-burn skill has always told seats to type by hand, and it
    stands on open PRs today.  ``v\\d+`` rather than today's
    ``MARKER_SCHEMA_VERSION`` is the version-bump rule this family needs and
    the exhaustion marker deliberately does not: an exhaustion gate carries
    the *policy* it gated under, so a bump means "re-decide", while these
    three carry only a seat's decision about one immutable SHA.  Pinning the
    reader to one version would silently lapse that decision on the next bump
    and re-summon a head someone deliberately stopped — which is the same
    class of defect as never reading the hold at all.
    """
    return re.compile(
        rf"{re.escape(HEAD_DISPOSITION_PREFIXES[kind])}"
        rf"(?:v\d+:)?{re.escape(head_sha)} -->"
    )


def product_gate_marker(head_sha: str) -> str:
    return f"{PRODUCT_GATE_MARKER_PREFIX}{MARKER_SCHEMA_VERSION}:{head_sha} -->"


def product_gate_comment_body(head_sha: str) -> str:
    """The once-per-head record that a burn completed as product-gate.

    The head is unchanged on purpose; without this marker the scheduled
    redelivery path treats that as a stall and re-wakes the burn seat.
    """
    return (
        "Review-loop: product-gate recorded for this head; the head is "
        "unchanged on purpose. Standing-wake redelivery must not treat this "
        "as an ignored wake.\n"
        f"{product_gate_marker(head_sha)}"
    )


def noise_marker(head_sha: str) -> str:
    return f"{NOISE_MARKER_PREFIX}{MARKER_SCHEMA_VERSION}:{head_sha} -->"


def noise_comment_body(head_sha: str) -> str:
    """The once-per-head record that a burn completed as all-noise.

    The head is unchanged on purpose; without this marker the scheduled
    redelivery path treats that as a stall and re-wakes the burn seat.
    """
    return (
        "Review-loop: noise recorded for this head; the head is "
        "unchanged on purpose. Standing-wake redelivery must not treat this "
        "as an ignored wake.\n"
        f"{noise_marker(head_sha)}"
    )


def hold_marker(head_sha: str) -> str:
    return f"{HOLD_MARKER_PREFIX}{MARKER_SCHEMA_VERSION}:{head_sha} -->"


def hold_comment_body(head_sha: str) -> str:
    """The once-per-head record that a seat handed this head to a human.

    The attention contract requires a burn seat to stop and raise a human gate
    for a decision it has no authority to take.  Nothing about that act reaches
    the belt: the head does not move, no verdict lands, and the scheduled leg
    reads an unreviewed head past the stall window as a stall and summons a
    reviewer — spending a review round on a head the gate has already declared
    unable to survive (sokrates#1107 round 5, 2026-08-22).  This marker is the
    gate's machine half.  It is head-scoped, so the push that answers the gate
    clears it with no second act by the seat.
    """
    return (
        "Review-loop: hold recorded for this head; a human gate stands above "
        "and the head is unchanged on purpose. No reviewer is to be summoned "
        "for this head.\n"
        f"{hold_marker(head_sha)}"
    )


def head_is_held(comments: Sequence[Mapping[str, Any]], head_sha: str) -> bool:
    """True when a trusted seat has held this exact head for a human."""
    return marker_comment_exists(comments, head_disposition_pattern("hold", head_sha))


def skip_marker(head_sha: str) -> str:
    return f"{SKIP_MARKER_PREFIX}{MARKER_SCHEMA_VERSION}:{head_sha} -->"


def review_skip_reason(commit_message: str) -> str | None:
    """The reason a commit gives for skipping the next review round, if it gives one.

    A ``Review-skip: <why>`` trailer line anywhere in the message; the last one
    wins. Absent, empty or whitespace-only means no skip was asked for.
    """
    reason: str | None = None
    for line in commit_message.splitlines():
        stripped = line.strip()
        if stripped.lower().startswith(REVIEW_SKIP_TRAILER.lower()):
            candidate = stripped[len(REVIEW_SKIP_TRAILER) :].strip()
            reason = candidate or None
    return reason


def skip_comment_body(head_sha: str, reason: str) -> str:
    """The once-per-head record that the seat judged the next round not worth its hour.

    Hákon's ruling (2026-09-06): when a defect still in the code would announce
    itself the first time it runs, execution is the review. The burn commit says
    so with a ``Review-skip:`` trailer; the push leg records it here instead of
    summoning, the scheduled leg reads the head's stillness as a decision like a
    hold, and the merge boundary takes this marker as the verdict limb — the
    head merges at green with zero threads.
    """
    return (
        "Review-loop: review round skipped for this head by the pushing seat — "
        f"{reason}. No reviewer is to be summoned for this head; it merges at the "
        "green boundary with zero open threads (Hákon's ruling, 2026-09-06).\n"
        f"{skip_marker(head_sha)}"
    )


def head_is_skipped(comments: Sequence[Mapping[str, Any]], head_sha: str) -> bool:
    """True when a trusted identity recorded that this exact head needs no round."""
    return marker_comment_exists(comments, head_disposition_pattern("skip", head_sha))


def head_disposed_at(
    kind: str, comments: Sequence[Mapping[str, Any]], head_sha: str
) -> datetime | None:
    """When a trusted seat last recorded this disposition for this exact head."""
    return trusted_marker_time(comments, head_disposition_pattern(kind, head_sha))


def current_run_id() -> str:
    """The workflow run posting this comment, when the process is one."""
    return os.environ.get("GITHUB_RUN_ID", "").strip()


def nudge_marker(head_sha: str, run_id: str = "") -> str:
    """Exact-head marker, stamped with the run that minted it when known.

    The nudge posts under ``CODEX_REVIEW_PAT``, which is the same login a
    seat's own ``gh`` token uses, so authorship cannot tell a scheduled nudge
    from a hand-typed one.  The run id makes provenance readable from the
    comment instead of reconstructible from run timings.  A non-numeric run id
    is dropped rather than embedded: the reader's suffix is ``run-\\d+``, and a
    marker its own reader cannot match would re-nudge the head forever.
    """
    stamp = f":run-{run_id}" if run_id.isdigit() else ""
    return f"{NUDGE_MARKER_PREFIX}{MARKER_SCHEMA_VERSION}:{head_sha}{stamp} -->"


def nudge_marker_pattern(head_sha: str) -> re.Pattern[str]:
    """Every nudge marker vintage for this head: unversioned, v2, run-stamped.

    Coverage that stops being recognised is a duplicate summon, so this reader
    is deliberately wider than any one writer: the unversioned form, any
    version, and with or without the run stamp.
    """
    return re.compile(
        rf"{re.escape(NUDGE_MARKER_PREFIX)}(?:v\d+:)?{re.escape(head_sha)}"
        r"(?::run-\d+)? -->"
    )


def nudge_comment_body(head_sha: str) -> str:
    """Codex trigger, the scope test it reviews under, and an exact-head marker
    so force-pushes cannot reuse it."""
    return (
        f"@codex review\n\n{SCOPE_TEST_REVIEWER}\n\n"
        f"{nudge_marker(head_sha, current_run_id())}"
    )


def redelivery_marker(head_sha: str, verdict_at: str) -> str:
    """Once-per-verdict marker: a later verdict on the same SHA is a new event."""
    return (
        f"{REDELIVERY_MARKER_PREFIX}{MARKER_SCHEMA_VERSION}:{head_sha}:{verdict_at} -->"
    )


def legacy_redelivery_marker(head_sha: str, verdict_at: str) -> str:
    return f"{REDELIVERY_MARKER_PREFIX}{head_sha}:{verdict_at} -->"


def redelivery_recorded(
    comments: Sequence[Mapping[str, Any]], head_sha: str, verdict_at: str
) -> bool:
    """True when this verdict on this head was already re-delivered (any vintage)."""
    return marker_comment_exists(
        comments,
        (
            redelivery_marker(head_sha, verdict_at),
            legacy_redelivery_marker(head_sha, verdict_at),
        ),
    )


def head_base_marker(head_sha: str, base_ref: str, base_sha: str) -> str:
    """v2 pins carry the base *ref* too: the closure predicate reads it."""
    return (
        f"{HEAD_BASE_MARKER_PREFIX}{MARKER_SCHEMA_VERSION}:"
        f"{head_sha}:{base_ref}:{base_sha} -->"
    )


def head_base_marker_for(head_sha: str) -> tuple[str, str]:
    """Prefixes matching any pin for this head, versioned or legacy."""
    return (
        f"{HEAD_BASE_MARKER_PREFIX}{MARKER_SCHEMA_VERSION}:{head_sha}:",
        f"{HEAD_BASE_MARKER_PREFIX}{head_sha}:",
    )


def head_base_recorded(comments: Sequence[Mapping[str, Any]], head_sha: str) -> bool:
    """True when the loop has already pinned this exact head's base, any vintage."""
    return marker_comment_exists(comments, head_base_marker_for(head_sha))


def head_base_comment_body(head_sha: str, base_ref: str, base_sha: str) -> str:
    return (
        "Review-loop: recorded contemporaneous base "
        f"`{base_ref}` @ `{base_sha}` for reviewed head `{head_sha}`.\n"
        f"{head_base_marker(head_sha, base_ref, base_sha)}"
    )


def recorded_head_bases(comments: Sequence[Mapping[str, Any]]) -> dict[str, str]:
    """Trusted pins of each reviewed head's contemporaneous base SHA.

    First pin for a head wins: that is the base that was live when the
    verdict was first accepted. A later force-push of the target does not
    rewrite the series bound. Both marker generations are read; a v2 pin and
    a legacy pin for the same head keep whichever came first in comment order.
    """
    trusted = trusted_control_logins()
    bases: dict[str, str] = {}
    for comment in comments:
        user = comment.get("user")
        if not isinstance(user, Mapping) or user.get("login") not in trusted:
            continue
        body = str(comment.get("body") or "")
        for v2 in HEAD_BASE_MARKER_V2_RE.finditer(body):
            head, _ref, base = v2.groups()
            if head not in bases:
                bases[head] = base
        for match in HEAD_BASE_MARKER_RE.finditer(body):
            head, base = match.group(1), match.group(2)
            if head == MARKER_SCHEMA_VERSION:
                continue  # the first two segments of a v2 pin, not a legacy pin
            if head not in bases:
                bases[head] = base
    return bases


def recorded_head_base_refs(comments: Sequence[Mapping[str, Any]]) -> dict[str, str]:
    """Trusted pins of each reviewed head's contemporaneous base *ref*.

    Only v2 pins carry a ref; a legacy pin contributes nothing here, so the
    closure predicate treats its head as having no recorded ref to compare.
    """
    trusted = trusted_control_logins()
    refs: dict[str, str] = {}
    for comment in comments:
        user = comment.get("user")
        if not isinstance(user, Mapping) or user.get("login") not in trusted:
            continue
        for v2 in HEAD_BASE_MARKER_V2_RE.finditer(str(comment.get("body") or "")):
            head, ref, _base = v2.groups()
            if head not in refs:
                refs[head] = ref
    return refs


def stale_base_ref_for_closure(
    comments: Sequence[Mapping[str, Any]], head_sha: str, live_base_ref: str
) -> str | None:
    """The recorded verdict-time base ref when it disagrees with the live one.

    The minimal review-subject predicate: an exact-head CLEAN was formed
    against the PR as targeted at verdict time. If the PR has since been
    retargeted (base *ref* changed — tip movement alone does not trip this),
    the head SHA alone no longer names what was reviewed, and closure must
    refuse rather than wake a seat with a stale claim. Refusing wakes nobody;
    the refusal is logged and a human resolves the retarget.
    """
    recorded = recorded_head_base_refs(comments).get(head_sha)
    if recorded and recorded != live_base_ref:
        return recorded
    return None


def base_retarget_after(
    github: GitHubApi, pr_number: int, verdict_time: str
) -> str | None:
    """The timestamp of a base-branch retarget newer than the verdict, if any.

    The pin comment cannot witness the FIRST closure after a retarget: the pin
    is written at hook time, so a verdict formed against the old target and a
    pin recorded after the retarget agree with each other and with the live
    base.  GitHub's issue events are the independent witness — a
    ``base_ref_changed`` event created after the verdict proves the review's
    subject is not the PR as now targeted.  Fetched only on the closure path,
    so the ordinary scan pays nothing.
    """
    verdict_at = result_event_time(verdict_time)
    for event in github.paginate(f"issues/{pr_number}/events"):
        if not isinstance(event, Mapping):
            continue
        if event.get("event") != "base_ref_changed":
            continue
        created = str(event.get("created_at") or "")
        # An undated verdict sorts to datetime.min, so any retarget event
        # refuses closure — the safe direction for an unwitnessable subject.
        if created and result_event_time(created) > verdict_at:
            return created
    return None


def record_reviewed_head_base(
    github: GitHubApi,
    pr_number: int,
    head_sha: str,
    base_ref: str,
    base_sha: str,
    *,
    repository: str,
    comments: Sequence[Mapping[str, Any]] | None = None,
) -> str:
    """Persist the base that was live when this head was reviewed.

    Deduplicates by head, not by ``(head, base)``: the first accepted pin
    is the contemporaneous one. A later pin after the target moved would
    record the wrong series bound.

    Returns a member of ``COMMENT_AT_HEAD_PUBLISHED`` when the pin is on the
    PR, and otherwise the chokepoint's refusal reason — see
    ``ensure_comment_at_head``.
    """
    existing = comments
    if existing is None:
        existing = github.paginate(f"issues/{pr_number}/comments")
    if head_base_recorded(existing, head_sha):
        return "existing"
    return ensure_comment_at_head(
        github,
        pr_number,
        head_base_marker_for(head_sha),
        head_base_comment_body(head_sha, base_ref, base_sha),
        expected_head=head_sha,
        repository=repository,
        action="head-base pin",
    )


def redelivery_comment_body(head_sha: str, verdict_at: str) -> str:
    """The once-per-verdict record that a standing verdict was re-delivered.

    Deliberately carries no ``@codex`` trigger: redelivery re-delivers attention
    to a seat, it never summons another review.  The nudge leg owns summoning.
    """
    return (
        "Review-loop: the standing verdict for this head was re-delivered to "
        f"#hive (original verdict `{verdict_at}`; the head has not moved "
        "since). One redelivery per standing verdict — a later verdict on this "
        "head, or a push, starts a fresh cycle.\n"
        f"{redelivery_marker(head_sha, verdict_at)}"
    )


def redelivery_notice(verdict_at: str) -> str:
    """The line that tells the receiving seat this wake is not a new dispatch."""
    return (
        f"REDELIVERY — restating a standing review-loop verdict first delivered "
        f"at `{verdict_at}`; the head has not moved since, so the action below "
        "is still outstanding. Per `universe/30-hive.md`, check whether the work "
        "already happened before redoing it: a repeated wake is never a second "
        "dispatch, and it adds no review round and no authority."
    )


def exhaustion_gate(
    *,
    pr_url: str,
    head_sha: str,
    reviewed_heads: int,
    reason: str,
) -> str:
    """A once-per-head, cold-answerable stop after bounded automation."""
    return (
        f"{exhaustion_marker(head_sha)}\n"
        "## Review loop exhausted — human decision required\n\n"
        f"PR: {pr_url}\n\n"
        f"Current head: `{head_sha}`\n\n"
        f"Automatic review rounds consumed: {reviewed_heads}/{MAX_REVIEW_ROUNDS}.\n\n"
        f"Why the loop stopped: {reason}\n\n"
        "This head is **not merge-ready**. The safe default is to leave it "
        "unmerged and stop automatic repair/re-review. Hákon: choose one of "
        "these explicit continuations:\n\n"
        "1. authorize one additional manual repair/re-review round outside the "
        "automatic loop;\n"
        "2. re-scope genuinely out-of-scope findings into named follow-up "
        "tickets, then request a fresh exact-head review; or\n"
        "3. close or defer the PR.\n\n"
        "A later merge still requires an exact-head clean review, green required "
        "checks, no conflicts, and separate merge authority."
        + (
            ""
            if retrospective_actor() is not None
            else (
                f"\n\nRetrospective: held — `{RETROSPECTIVE_ACTOR_ENV}` names no seat "
                "(Hákon's ruling, 2026-09-07: no exhaustion testimony during the "
                "thirteen-lanes crunch). The gate stands on its own; nobody is woken."
            )
        )
    )


def ensure_exhaustion_gate_at_head(
    github: GitHubApi,
    pr_number: int,
    gate: str,
    *,
    head_sha: str,
    repository: str,
    action: str,
) -> str:
    """Post an exhaustion gate once per ``(head, policy)``.

    Terminal (same policy, or an honored legacy marker) deduplicates; a
    stale-policy marker does not — the situation it gated was measured against
    a bound that no longer exists, so the gate is re-stated under the current
    policy rather than silently inherited.

    Same return contract as ``ensure_comment_at_head``: a member of
    ``COMMENT_AT_HEAD_PUBLISHED``, or the chokepoint's refusal reason.
    """
    comments = github.paginate(f"issues/{pr_number}/comments")
    state = exhaustion_marker_state(comments, head_sha)
    if state == "terminal":
        return "existing"
    if state == "stale-policy":
        print(
            f"re-posting exhaustion gate for {repository}#{pr_number} "
            f"(head={head_sha}): the prior gate recorded a different policy"
        )
    refusal: list[str] = []
    if (
        refresh_pr_at_head(
            github,
            pr_number,
            head_sha,
            repository,
            action=action,
            on_ignored=refusal.append,
        )
        is None
    ):
        return refusal[0] if refusal else "refused"
    github.post(f"issues/{pr_number}/comments", {"body": gate})
    return "posted"


def ensure_comment_at_head(
    github: GitHubApi,
    pr_number: int,
    marker: str | Sequence[str],
    body: str,
    *,
    expected_head: str,
    repository: str,
    action: str,
) -> str:
    """Deduplicate, then revalidate the live head immediately before posting.

    Returns ``"existing"`` or ``"posted"`` — both in
    ``COMMENT_AT_HEAD_PUBLISHED`` — or the chokepoint's own refusal reason
    (``head-moved`` / ``pr-closed`` / ``pr-merged``).  A single ``"stale"``
    sentinel was the reason the belt recorded a merge race as a push: the
    caller could only guess, and every caller guessed ``head-moved``
    (KRA-1226).
    """
    comments = github.paginate(f"issues/{pr_number}/comments")
    if marker_comment_exists(comments, marker):
        return "existing"
    refusal: list[str] = []
    if (
        refresh_pr_at_head(
            github,
            pr_number,
            expected_head,
            repository,
            action=action,
            on_ignored=refusal.append,
        )
        is None
    ):
        # The chokepoint names every refusal it returns, so the fallback is
        # unreachable today; it stays a refusal rather than a wrong reason.
        return refusal[0] if refusal else "refused"
    github.post(f"issues/{pr_number}/comments", {"body": body})
    return "posted"


def trusted_control_logins() -> frozenset[str]:
    """Identities whose control markers are authoritative for deduplication.

    Two identities write control markers. The workflow itself posts exhaustion
    gates on the event path; the scheduled path authenticates as the
    Codex-connected account (KRA-1032) and posts both nudges and gates. They are
    one trust domain, so a marker written by either must suppress the other.

    Splitting them is the defect: whichever path does not recognise the other's
    marker re-posts it, giving one head two nudges or two exhaustion gates. Both
    halves therefore read this one set rather than each naming its own author.
    """
    logins = [
        os.environ.get("WORKFLOW_LOGIN", WORKFLOW_LOGIN),
        os.environ.get("CODEX_REVIEW_AUTHOR", CODEX_REVIEW_AUTHOR),
    ]
    return frozenset(login for login in logins if login)


def _marker_forms(
    marker: str | re.Pattern[str] | Sequence[str | re.Pattern[str]],
) -> list[str | re.Pattern[str]]:
    return [marker] if isinstance(marker, (str, re.Pattern)) else list(marker)


def _marker_in(body: str, forms: Sequence[str | re.Pattern[str]]) -> bool:
    """One reader for both marker predicates below.

    A literal is the marker exactly as some writer emits it; a pattern is what a
    reader needs when the writer's version is derived from a constant that can
    advance underneath it.
    """
    return any(
        form.search(body) is not None if isinstance(form, re.Pattern) else form in body
        for form in forms
    )


def marker_comment_exists(
    comments: Sequence[Mapping[str, Any]],
    marker: str | re.Pattern[str] | Sequence[str | re.Pattern[str]],
) -> bool:
    """Trust a control marker only when a trusted control identity authored it.

    ``marker`` may be several equivalent forms (versioned plus legacy, literal
    or pattern); any one of them counts.
    """
    forms = _marker_forms(marker)
    trusted = trusted_control_logins()
    for comment in comments:
        user = comment.get("user")
        if not isinstance(user, Mapping) or user.get("login") not in trusted:
            continue
        if _marker_in(str(comment.get("body") or ""), forms):
            return True
    return False


def trusted_marker_time(
    comments: Sequence[Mapping[str, Any]],
    marker: str | re.Pattern[str] | Sequence[str | re.Pattern[str]],
) -> datetime | None:
    """Latest created_at of a trusted comment carrying this marker, if dated.

    A form may be a literal — the marker exactly as its writer emits it today —
    or a compiled pattern, for a reader that must keep recognising the marker
    across a writer-version bump rather than only its own vintage.
    """
    forms = _marker_forms(marker)
    trusted = trusted_control_logins()
    latest: datetime | None = None
    unstamped = datetime.min.replace(tzinfo=timezone.utc)
    for comment in comments:
        user = comment.get("user")
        if not isinstance(user, Mapping) or user.get("login") not in trusted:
            continue
        if not _marker_in(str(comment.get("body") or ""), forms):
            continue
        raw = comment.get("created_at")
        if not isinstance(raw, str) or not raw.strip():
            continue
        stamped = result_event_time(raw)
        if stamped == unstamped:
            continue
        if latest is None or stamped > latest:
            latest = stamped
    return latest


def refresh_pr_at_head(
    github: GitHubApi,
    pr_number: int,
    expected_head: str,
    repository: str,
    *,
    action: str = "Codex result",
    on_ignored: Callable[[str], None] | None = None,
    require_open: bool = True,
) -> Mapping[str, Any] | None:
    """Re-read the live PR immediately before publishing a verdict.

    Two facts decide publishability and both are decided here, not at the call
    sites: the head must still be the reviewed one, and the PR must still be
    open.  Liveness belongs at the chokepoint because this is the last read
    before any publish, so it also closes the window where the PR merges
    between the Codex event firing and the verdict being published — the window
    that put an exhaustion gate on an already-merged PR three minutes after the
    merge, asking a human for a decision already taken (KRA-1226).  A per-path
    guard cannot close that window for the paths that do not carry one.

    ``require_open`` is that rule's one exception, and it defaults to enforcing
    it so a new caller inherits the guard rather than the hole.  It is for a
    publication whose *subject* is a dead PR: the retrospective chase asks
    whether testimony arrived, gates nothing, and is deliberately swept over
    recently CLOSED pull requests (KRA-1223), so refusing it on closure would
    delete the leg rather than protect it.  A verdict wake has no such reading
    — it is void the moment the PR is not open — and must never pass ``False``.

    ``on_ignored`` receives the refusal reason for callers that record it; the
    printed line is the unconditional record (R-3).
    """
    pr_state = github.get(f"pulls/{pr_number}")
    if not isinstance(pr_state, Mapping):
        raise TypeError("pull request lookup did not return an object")
    head = pr_state.get("head")
    if not isinstance(head, Mapping):
        raise TypeError("live pull_request.head is missing")
    current_head = str(head["sha"])
    if current_head != expected_head:
        print(
            f"ignored {action} after head moved for {repository}#{pr_number} "
            f"(review={expected_head}, current={current_head})"
        )
        if on_ignored is not None:
            on_ignored("head-moved")
        return None
    if require_open and str(pr_state.get("state") or "") != "open":
        # ``state`` alone decides the refusal; the word only names it, so a
        # reader of the job log can tell a merge race from an abandoned PR.
        # Same predicate shape as the belt-outcome telemetry: this endpoint
        # carries ``merged``, the list endpoint carries only ``merged_at``.
        disposition = (
            "merged"
            if bool(pr_state.get("merged") or pr_state.get("merged_at"))
            else "closed"
        )
        print(
            f"ignored {action} on a {disposition} {repository}#{pr_number} "
            f"(head={expected_head})"
        )
        if on_ignored is not None:
            on_ignored(f"pr-{disposition}")
        return None
    return pr_state


def pr_base(pr_state: Mapping[str, Any]) -> tuple[str, str]:
    """Return the live PR's ``(base.ref, base.sha)``.

    Burn and retrospective wakes embed both so a seat that can fetch the
    repo but cannot call the GitHub API — Talos v1 has no ``gh`` — can
    still name the declared base.  ``origin/HEAD`` is the wrong tree on a
    stacked or release-branch PR.
    """
    base = pr_state.get("base")
    if not isinstance(base, Mapping):
        raise TypeError("live pull_request.base is missing")
    ref = str(base.get("ref") or "").strip()
    sha = str(base.get("sha") or "").strip()
    if not ref or not sha:
        raise TypeError("live pull_request.base is missing ref or sha")
    return ref, sha


def finding_blocks(
    findings: Sequence[Mapping[str, Any]], *, max_body: int = 3500
) -> list[str]:
    blocks: list[str] = []
    for index, finding in enumerate(findings, start=1):
        body = str(finding.get("body") or "").strip()
        if len(body) > max_body:
            body = f"{body[: max_body - 1]}…"
        blocks.append(
            f"### Finding {index} — {finding.get('path', '?')}:{finding.get('line', '?')}\n{body}\n"
        )
    return blocks


def wake_envelope_line(text: str) -> str:
    """First WAKE:/NEXT line — the envelope Hive's ``parseAddressedWake`` binds.

    That parser scans every line (``src/addressing.ts``), so a continuation
    that starts with only a label lets an embedded finding line such as
    ``WAKE: talos`` or ``NEXT fable`` become the routing envelope and steal
    the chunk from the intended seat.
    """
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.upper().startswith("WAKE:") or stripped.upper().startswith("NEXT "):
            return stripped
    return ""


def chunk_digest(
    header: str,
    blocks: Sequence[str],
    *,
    label: str,
    budget: int = DIGEST_CHUNK_BUDGET,
) -> list[str]:
    """Split a digest across Slack messages; ``label`` names it in continuations."""
    if not blocks:
        return [f"{header}(no {label} entries)"]
    envelope = wake_envelope_line(header)
    messages: list[str] = []
    prefix = header
    current: list[str] = []
    used = len(prefix)
    for block in blocks:
        separator = 1 if current else 0
        # A block that does not fit beside what the page already holds starts
        # the next page — including when the page holds only the header, so a
        # long header never pushes the first block over the budget.
        if used + separator + len(block) > budget:
            messages.append(prefix + "\n".join(current))
            continued = f"({label} continued — part {len(messages) + 1})\n\n"
            prefix = f"{envelope}\n\n{continued}" if envelope else continued
            current = [block]
            used = len(prefix) + len(block)
        else:
            current.append(block)
            used += separator + len(block)
    if current:
        messages.append(prefix + "\n".join(current))
    return messages


def build_burn_messages(
    *,
    findings: Sequence[Mapping[str, Any]],
    review_state: str,
    pr_url: str,
    branch: str,
    head_sha: str,
    base_ref: str,
    base_sha: str,
    repository: str,
    author: str,
    author_actor: str,
    review_round: int,
    history: Sequence[Mapping[str, Any]] | None = None,
    substitute: Mapping[str, Any] | None = None,
    cast: tuple[str, str] | None = None,
    effort: str | None = None,
) -> list[str]:
    if substitute is None:
        counts = severity_counts(findings)
        verdict = (
            f"Codex findings: {counts['p1']} P1 / {counts['p2']} P2 / "
            f"{counts['p3']} P3 (review state: {review_state})."
        )
    else:
        # A substitute verdict: counts come from the marker (deterministic),
        # and the digest is the substitute's verdict comment verbatim — the
        # loop never re-parses seat prose into structured findings.
        counts = dict(substitute["counts"])
        verdict = (
            f"Substitute ({substitute['actor']}) findings: {counts['p1']} P1 "
            f"/ {counts['p2']} P2 / {counts['p3']} P3 (marker verdict; the "
            "digest below is the substitute's verdict comment, verbatim)."
        )
        if findings:
            verdict += (
                f" This head also carries {len(findings)} Codex inline "
                "finding(s) from an earlier review — included below; burn "
                "the union."
            )
    evidence_heading = (
        "## Per-round history, then the current head's findings\n"
        if history
        else "## Finding digest\n"
    )
    actor, cast_note = cast if cast is not None else (burn_actor(), "")
    # The bare `Effort:` line is the edge's exact grammar (hive#49); it sits
    # directly under the envelope so no digest line can be mistaken for it.
    effort_line = f"Effort: {effort}\n" if effort else ""
    cast_paragraph = f"{cast_note}\n" if cast_note else ""
    header = (
        f"WAKE: {actor}\n{effort_line}\n"
        f"Burn seat `{actor}` — load skill `talos-burn` and burn these findings.\n\n"
        f"{cast_paragraph}"
        f"{SCOPE_TEST_BURNER}\n\n"
        f"Review-loop hook: {verdict} {MERGE_REGIME}\n\n"
        f"PR: {pr_url}\n"
        f"Branch: `{branch}`\n"
        f"Head: `{head_sha}`\n"
        f"Base: `{base_ref}` @ `{base_sha}`\n"
        f"Repo: `{repository}`\n"
        f"Author: `{author}` (seat `{author_actor}`)\n\n"
        f"Exact-head review: `yes` — round {review_round}/{MAX_REVIEW_ROUNDS}.\n"
        "Any repair changes the head and invalidates this review closure. Push "
        "one coherent burn, then wait for a fresh exact-head Codex review.\n\n"
        "Doctrine: in-scope findings are fixed unless tagged `product-gate` or `noise`; "
        "out-of-scope findings become follow-up tickets, then seek fresh "
        "exact-head closure. Never interleave fixing with merging. "
        "If this seat cannot access the repo, use talos-burn's explicit Hive handoff to the authoring seat with "
        "the digest intact (R-3: failures stay visible).\n\n"
        f"{evidence_heading}"
    )
    blocks = [
        *(round_history_blocks(history, head_sha) if history else ()),
        *(
            finding_blocks(findings)
            if substitute is None
            else [
                *finding_blocks(findings),
                *prior_substitute_digest_blocks(history or (), head_sha),
                *bounded_digest_blocks(str(substitute["body"])),
            ]
        ),
    ]
    return chunk_digest(header, blocks, label="finding digest")


def bounded_digest_blocks(body: str, *, max_body: int = 3500) -> list[str]:
    """Split a raw substitute digest so ``chunk_digest`` can place it.

    ``chunk_digest`` never splits inside a block. Codex findings are already
    bounded by ``finding_blocks``; a substitute verdict is one comment, so an
    oversized body has to be pre-split or the Slack post fails after the
    head already counts as reviewed.
    """
    text = str(body or "")
    if not text:
        return [""]
    if len(text) <= max_body:
        return [text]
    blocks: list[str] = []
    remaining = text
    while remaining:
        if len(remaining) <= max_body:
            blocks.append(remaining)
            break
        window = remaining[:max_body]
        cut = window.rfind("\n\n")
        if cut < max_body // 2:
            cut = window.rfind("\n")
        if cut < max_body // 2:
            cut = max_body
        blocks.append(remaining[:cut])
        remaining = remaining[cut:].lstrip("\n")
    return blocks


def prior_substitute_digest_blocks(
    history: Sequence[Mapping[str, Any]], current_head: str
) -> list[str]:
    """Earlier substitute-round comment bodies, already bounded for chunking."""
    blocks: list[str] = []
    wanted = current_head.lower()
    for entry in history:
        if str(entry.get("head") or "").lower() == wanted:
            continue
        digest = str(entry.get("digest") or "")
        if not digest:
            continue
        heading = (
            f"### Round {entry['round']}/{entry['rounds']} substitute digest "
            f"— `{entry['head']}`\n"
        )
        continued = (
            f"### Round {entry['round']}/{entry['rounds']} substitute digest "
            f"— `{entry['head']}` (continued)\n"
        )
        room = max(1, 3500 - max(len(heading), len(continued)))
        parts = bounded_digest_blocks(digest, max_body=room)
        blocks.append(heading + parts[0] + "\n")
        for part in parts[1:]:
            blocks.append(continued + part + "\n")
    return blocks


def location_lines(
    locations: Sequence[str], *, max_len: int = ROUND_LOCATION_LINE_BUDGET
) -> list[str]:
    """Split a Locations line so one round cannot overrun the digest budget."""
    prefix = "Locations: "
    room = max_len - len(prefix)
    if room < 1:
        raise ValueError("max_len is too small for a Locations line")
    if not locations:
        return []
    lines: list[str] = []
    current: list[str] = []
    used = 0

    def fit(location: str) -> str:
        if len(location) <= room:
            return location
        return f"{location[: room - 1]}…"

    for location in locations:
        item = fit(str(location))
        extra = len(item) if not current else len(item) + 2
        if current and used + extra > room:
            lines.append(prefix + ", ".join(current))
            current = [item]
            used = len(item)
        else:
            current.append(item)
            used += extra
    if current:
        lines.append(prefix + ", ".join(current))
    return lines


def contemporaneous_base_line(entry: Mapping[str, Any]) -> str:
    """Name this head's recorded series bound, or refuse to invent one."""
    base = str(entry.get("base") or "").strip()
    if base:
        return f"Base at review: `{base}`"
    return (
        "Base at review: unavailable — do not derive from the live Base; "
        "stop classification"
    )


def round_history_blocks(
    history: Sequence[Mapping[str, Any]], current_head: str
) -> list[str]:
    """Render self-labelling blocks per round so any chunk split stays legible.

    A single review can name enough locations to exceed ``chunk_digest``'s
    budget. Locations are split into continued blocks, each still labelled
    with the round and head.
    """
    blocks: list[str] = []
    for entry in history:
        counts = entry["counts"]
        head = str(entry["head"])
        marker = " **(current head)**" if head == current_head else ""
        title = f"### Round {entry['round']}/{entry['rounds']} — `{head}`{marker}"
        base_line = contemporaneous_base_line(entry)
        if not counts["total"]:
            blocks.append(f"{title}\n{base_line}\nVerdict: {entry['verdict']}.\n")
            continue
        verdict = (
            f"Verdict: {entry['verdict']} — {counts['p1']} P1 / "
            f"{counts['p2']} P2 / {counts['p3']} P3 ({counts['total']} total)."
        )
        loc_lines = location_lines([str(item) for item in entry["locations"]])
        if not loc_lines:
            blocks.append(f"{title}\n{base_line}\n{verdict}\n")
            continue
        blocks.append(f"{title}\n{base_line}\n{verdict}\n{loc_lines[0]}\n")
        continued = f"{title} (locations continued)"
        for loc_line in loc_lines[1:]:
            blocks.append(f"{continued}\n{loc_line}\n")
    return blocks


def build_retrospective_messages(
    *,
    findings: Sequence[Mapping[str, Any]],
    history: Sequence[Mapping[str, Any]],
    pr_url: str,
    pr_number: int,
    branch: str,
    head_sha: str,
    base_ref: str,
    base_sha: str,
    repository: str,
    author: str,
    author_actor: str,
    review_round: int,
    substitute: Mapping[str, Any] | None = None,
    actor: str | None = None,
) -> list[str]:
    """Ask the retrospective seat why burning could not close this PR, and what generalises."""
    seat = actor or RETROSPECTIVE_ACTOR
    header = (
        f"WAKE: {seat}\n\n"
        "Review-loop hook: the bounded automatic loop is exhausted — "
        f"{review_round} reviewed head(s) consumed against an automatic bound "
        f"of {MAX_REVIEW_ROUNDS}, and burning did not close this PR. You are "
        "asked for a retrospective verdict. This wake carries no repair, "
        "re-review, or merge authority.\n\n"
        f"{SCOPE_TEST} Test first whether the rounds were spent on findings "
        "that fail it — scope, not code, is then the cause.\n\n"
        f"PR: {pr_url}\n"
        f"Branch: `{branch}`\n"
        f"Head: `{head_sha}`\n"
        f"Base: `{base_ref}` @ `{base_sha}`\n"
        f"Repo: `{repository}`\n"
        f"Author: `{author}` (seat `{author_actor}`)\n"
        f"Rounds consumed: {review_round} (automatic bound: "
        f"{MAX_REVIEW_ROUNDS}) — a PR whose rounds predate the bound reads "
        "above it.\n\n"
        "The human gate is already on the PR and the authoring seat is already "
        "woken; nothing waits on this verdict.\n\n"
        "What is asked:\n\n"
        "1. **Classify each reviewed head** as *original*, *repair*, or "
        "*no-op* before naming a cause. Give repairs-per-round, never "
        "rounds alone. The two-range form is `git range-diff "
        "<old-base>..<old-head> <new-base>..<new-head>` over each head's "
        "full series — not `git diff <head>^ <head>`, which sees only the "
        "tip and can hide an earlier repair in a multi-commit burn. Use "
        "each round's recorded contemporaneous base as that head's series "
        "bound. The live `Base: <base-ref> @ <base-sha>` line is only the "
        "current declared base (never `origin/HEAD`); do not derive an "
        "earlier series from it. After the target is force-pushed or "
        "rebased, `git merge-base <old-head> <live-base>` can fall back "
        "before commits that belonged to the old base and corrupt the "
        "classification. If a compared head has no recorded "
        "contemporaneous base, report the gap and stop; do not invent a "
        "range:\n\n"
        "    git fetch origin <old-base> <old-head> <new-base> <new-head>\n"
        "    git range-diff <old-base>..<old-head> "
        "<new-base>..<new-head>\n\n"
        "Do not pass the two tips to `git merge-base` with each other — "
        "that common ancestor is the wrong range on a stacked or release "
        "branch. If a fetch fails, report the gap and stop; "
        "do not invent a range. `=` means replayed unchanged; `!` means "
        "read the diff before counting a repair. Head-to-head `git diff` "
        "is worthless across a rebase.\n"
        "2. **Name the structural cause** — which property was being "
        "established, and why repeated repair could not establish it. "
        '"No structural cause; the finding classes were independent" is a '
        "valid and valuable verdict — some PRs are simply large. Never "
        "conclude from absence: report the gap and stop.\n"
        "3. **Codify what generalises** — a new scar-assert on an existing "
        "skill (preferred; `skills/writing-skills/SKILL.md` §4 makes "
        "refinement the default) or, rarely, a new skill. Provenance is "
        "mandatory: PR, findings, round count, claimed scope. Silence is a "
        "legitimate outcome — a one-off does not earn a corpus entry, and a "
        "corpus of noise is worse than a small one.\n"
        "4. **Post the verdict on the PR** so it is attached to the evidence, "
        "not only to this thread. Write it to a file, then post the FILE:\n\n"
        f"    gh pr comment {pr_number} -R {repository} --body-file <path>\n\n"
        "`--body @<path>` is not an alternative: `gh` has no `@file` idiom, "
        "so it posts the literal string `@<path>` and the verdict never "
        "leaves the disk — that is how one sat unread for eight days "
        "(sokrates#1113). End the posted body with exactly:\n\n"
        f"    {retrospective_marker(head_sha)}\n\n"
        "That marker is the loop's only evidence of delivery: without it "
        f"this PR is chased in {RETROSPECTIVE_DELIVERY_SECONDS // 60} "
        "minutes and then flagged on the PR as missing testimony, however "
        "complete the verdict in this thread is. Skill changes ride a "
        "review-ready PR to weave-doctrine; the composed boundary admits the "
        "merge, and Hákon's veto is retrospective.\n\n"
        "The evidence below is the shape of the sequence: did severity fall, "
        "did the same file keep reappearing, did each burn draw new findings.\n\n"
        "## Per-round history, then the current head's findings\n"
    )
    blocks = [
        *round_history_blocks(history, head_sha),
        *(
            finding_blocks(findings)
            if substitute is None
            else [
                *finding_blocks(findings),
                *prior_substitute_digest_blocks(history, head_sha),
                *bounded_digest_blocks(str(substitute["body"])),
            ]
        ),
    ]
    return chunk_digest(header, blocks, label="retrospective evidence")


def explicit_clean_signal(
    review: Mapping[str, Any],
    conversation_comments: Sequence[Mapping[str, Any]],
    github: GitHubApi,
    codex_login: str,
    head_sha: str,
) -> bool:
    """True only when a recognized clean comment covers this head.

    An empty findings list is not evidence of CLEAN. The review body itself
    may be a clean comment, or a conversation comment may already have
    established the same head.

    A review body in the exact-head shape names its own head, and
    ``route_review`` verifies only the review object's ``commit_id`` — so the
    two can disagree, and the prose is the claim. This channel binds the
    sentence exactly as ``clean_comment_commitish`` does for the comment
    channel: sentence-first, fail closed. The binding itself is
    ``clean_verdict_binds_head``, shared with the result-event stream so this
    route and that classification cannot answer differently.
    """
    wanted = head_sha.lower()
    if clean_verdict_binds_head(str(review.get("body") or ""), wanted):
        return True
    return any(
        clean_comment_head(github, comment, codex_login) == wanted
        for comment in conversation_comments
    )


def publish_exhaustion_retrospective(
    slack: SlackApi,
    *,
    github: GitHubApi,
    findings: Sequence[Mapping[str, Any]],
    history: Sequence[Mapping[str, Any]],
    pr_url: str,
    branch: str,
    head_sha: str,
    repository: str,
    author: str,
    author_actor: str,
    review_round: int,
    pr_number: int,
    base_ref: str,
    base_sha: str,
    substitute: Mapping[str, Any] | None = None,
) -> None:
    """Wake Theoros after an exhaustion gate. Shared by ``route`` and ``nudge``.

    Slack first, then the receipt — the same publication rule as every other
    wake leg.  Receipt-first would let a Slack failure leave the PR claiming
    testimony was requested when no seat was ever asked, and the chase leg
    would then hound a seat that owes nothing.  This way a receipt failure
    raises out of the caller (R-3) and the worst case is the status quo ante:
    the wake landed and no chase can see it.

    A withheld dispatch propagates: the receipt below records that a seat was
    asked, and the chase leg dates its window from it, so a receipt written
    for a wake nobody received would hound a seat that owes nothing.
    """
    actor = retrospective_actor()
    if actor is None:
        # The hold (Hákon, 2026-09-07): the gate stands on its own and nobody
        # is asked, so no receipt is written and no chase can ever start.
        print(
            f"retrospective held for {repository}#{pr_number} (head={head_sha}): "
            f"{RETROSPECTIVE_ACTOR_ENV} names no seat; the gate stands, nobody is woken"
        )
        belt().event(
            "belt.retrospective.held",
            **{
                "logfire.msg": f"#{pr_number} retrospective held",
                "pull_request": pr_number,
                "head_sha": head_sha,
                "rounds_consumed": len(history),
            },
        )
        return
    post_threaded_messages(
        slack,
        build_retrospective_messages(
            findings=findings,
            history=history,
            pr_url=pr_url,
            pr_number=pr_number,
            branch=branch,
            head_sha=head_sha,
            base_ref=base_ref,
            base_sha=base_sha,
            repository=repository,
            author=author,
            author_actor=author_actor,
            review_round=review_round,
            substitute=substitute,
            actor=actor,
        ),
        github=github,
        repository=repository,
        pr_number=pr_number,
        head_sha=head_sha,
        decision="exhaustion_retrospective",
    )
    print(
        f"woke {actor} for {repository}#{pr_number} retrospective "
        f"(rounds={len(history)})"
    )
    # Once per head, however many times the wake is re-sent.  The retry
    # contract deliberately re-wakes on an existing gate, and a second receipt
    # would not merely duplicate a comment: the chase leg dates the delivery
    # window from the latest receipt, so every retry would silently push the
    # window forward and a never-delivered verdict could go unchased forever.
    # The request happened once; the receipt records that once.
    if retrospective_requested(
        github.paginate(f"issues/{pr_number}/comments"), head_sha
    ):
        print(
            f"retrospective request already recorded for {repository}#{pr_number} "
            f"(head={head_sha}); delivery window not re-anchored"
        )
        return
    github.post(
        f"issues/{pr_number}/comments",
        {"body": retrospective_wake_receipt_body(head_sha, actor)},
    )


def clean_wake_message(
    *,
    author_actor: str,
    author: str,
    head_sha: str,
    review_round: int,
    review_state: str,
    pr_url: str,
    branch: str,
    verdict_source: str = "Codex review",
) -> str:
    return (
        f"WAKE: {author_actor}\n\n"
        f"Review-loop hook: {verdict_source} is CLEAN on the exact current head "
        f"`{head_sha}` (round {review_round}/{MAX_REVIEW_ROUNDS}; review "
        f"state: {review_state}). {MERGE_REGIME}\n\n"
        f"PR: {pr_url} (branch `{branch}`, author `{author}` / seat "
        f"`{author_actor}`).\n"
        "Boundary: exact-head CLEAN closes review only. Compose the rest "
        "before merging — green required checks on this same SHA, no "
        "conflicts — and never carry either across a head change. Anything "
        "short of the full boundary stays ready-for-review."
    )


def route_review(event: Mapping[str, Any] | None = None) -> None:
    event = event or load_event()
    review = event.get("review")
    pull_request = event.get("pull_request")
    if not isinstance(review, Mapping) or not isinstance(pull_request, Mapping):
        raise TypeError("event does not contain a review and pull_request")
    review_user = review.get("user")
    codex_login = os.environ.get("CODEX_LOGIN", CODEX_LOGIN)
    if not isinstance(review_user, Mapping) or review_user.get("login") != codex_login:
        print("ignored non-Codex review")
        belt_ignored("non-codex-review")
        return
    if is_quota_refusal_body(str(review.get("body") or "")):
        print("ignored Codex quota-refusal review")
        belt().event(
            "belt.refusal.observed",
            **{
                "logfire.msg": "Codex quota refusal observed on a review",
                "channel": "review",
                "pull_request": int(pull_request.get("number") or 0),
            },
        )
        return

    repository = required_env("GITHUB_REPOSITORY")
    github = GitHubApi(required_env("GITHUB_TOKEN"), repository)
    pr_number = int(pull_request["number"])
    pr_state = github.get(f"pulls/{pr_number}")
    if not isinstance(pr_state, Mapping):
        raise TypeError("pull request lookup did not return an object")
    head = pr_state.get("head")
    if not isinstance(head, Mapping):
        raise TypeError("live pull_request.head is missing")
    head_sha = str(head["sha"])
    review_head_sha = str(review.get("commit_id") or "").strip()
    if not review_head_sha:
        raise TypeError("Codex review commit_id is missing")
    if review_head_sha != head_sha:
        print(
            f"ignored stale Codex review for {repository}#{pr_number} "
            f"(review={review_head_sha}, current={head_sha})"
        )
        belt_ignored(
            "stale-verdict-head",
            pull_request=pr_number,
            head_sha=head_sha,
            verdict_head=review_head_sha,
        )
        return

    resolved = author_for_pr(github, pr_number, head_sha, pr_state)
    if resolved is None:
        print("non-seat author - no wake")
        belt_ignored("non-seat-author", pull_request=pr_number, head_sha=head_sha)
        return
    author, author_actor = resolved
    if loop_exempt_pr(github, pr_number):
        print(
            f"loop-exempt PR {repository}#{pr_number} - every touched path "
            "sits under a corpus root with its own gate; no wake"
        )
        belt_ignored("loop-exempt-pr", pull_request=pr_number, head_sha=head_sha)
        return
    review_comments = github.paginate(f"pulls/{pr_number}/comments")
    findings = review_findings(review_comments, int(review["id"]), codex_login)
    reviews = github.paginate(f"pulls/{pr_number}/reviews")
    conversation_comments = github.paginate(f"issues/{pr_number}/comments")
    result_events = codex_result_events(
        github,
        [*reviews, review],
        conversation_comments,
        codex_login,
        pr_number=pr_number,
        review_comments=review_comments,
    )
    reviewed_heads = result_heads_from_events(result_events)
    review_round = result_round_for_head(reviewed_heads, review_head_sha)
    refreshed_pr = refresh_pr_at_head(
        github,
        pr_number,
        review_head_sha,
        repository,
        on_ignored=lambda reason: belt_ignored(
            reason, pull_request=pr_number, head_sha=review_head_sha
        ),
    )
    if refreshed_pr is None:
        return
    pr_state = refreshed_pr
    refreshed_head = pr_state.get("head")
    assert isinstance(refreshed_head, Mapping)
    branch = str(refreshed_head["ref"])
    pr_url = str(pr_state.get("html_url") or pull_request["html_url"])
    review_state = str(review.get("state") or "unknown")
    slack = SlackApi(required_env("HIVE_BOT_TOKEN"), required_env("HIVE_CHANNEL"))
    base_ref, base_sha = pr_base(pr_state)
    pin_state = record_reviewed_head_base(
        github,
        pr_number,
        head_sha,
        base_ref,
        base_sha,
        repository=repository,
        comments=conversation_comments,
    )
    if pin_state not in COMMENT_AT_HEAD_PUBLISHED:
        belt_ignored(pin_state, pull_request=pr_number, head_sha=head_sha)
        return

    if not findings:
        stale_ref = stale_base_ref_for_closure(
            conversation_comments, head_sha, base_ref
        )
        if stale_ref is not None:
            print(
                f"refused clean closure for {repository}#{pr_number}: head "
                f"{head_sha} was reviewed against base ref `{stale_ref}` but "
                f"the PR now targets `{base_ref}` — the head SHA alone no "
                "longer names the reviewed subject; resolve the retarget and "
                "request a fresh exact-head review"
            )
            belt().event(
                "belt.closure.refused",
                **{
                    "logfire.msg": "clean closure refused: stale-base-ref",
                    "reason": "stale-base-ref",
                    "pull_request": pr_number,
                    "head_sha": head_sha,
                    "base_ref": base_ref,
                },
            )
            return
        retargeted_at = base_retarget_after(
            github, pr_number, str(review.get("submitted_at") or "")
        )
        if retargeted_at is not None:
            print(
                f"refused clean closure for {repository}#{pr_number}: the PR "
                f"base was retargeted at `{retargeted_at}`, after this "
                "verdict was formed — the review's subject is not the PR as "
                "now targeted; request a fresh exact-head review"
            )
            belt().event(
                "belt.closure.refused",
                **{
                    "logfire.msg": "clean closure refused: base-retargeted",
                    "reason": "base-retargeted",
                    "pull_request": pr_number,
                    "head_sha": head_sha,
                    "base_ref": base_ref,
                },
            )
            return
        if explicit_clean_signal(
            review,
            conversation_comments,
            github,
            codex_login,
            head_sha,
        ):
            belt_verdict(
                pr_number=pr_number,
                head_sha=head_sha,
                verdict_kind="clean",
                decision="clean_wake",
                source_event_at=review.get("submitted_at"),
                review_round=review_round,
                rounds_consumed=len(reviewed_heads),
                author_seat=author_actor,
                review_state=review_state,
                base_ref=base_ref,
                base_sha=base_sha,
                head_commit_age=belt().head_commit_age_seconds(github, head_sha),
            )
            if deliver_wake(
                lambda: slack.post_message(
                    clean_wake_message(
                        author_actor=author_actor,
                        author=author,
                        head_sha=head_sha,
                        review_round=review_round,
                        review_state=review_state,
                        pr_url=pr_url,
                        branch=branch,
                    )
                ),
                github=github,
                repository=repository,
                pr_number=pr_number,
                head_sha=head_sha,
                decision="clean_wake",
            ):
                print(f"woke {author_actor} for {repository}#{pr_number} (findings=0)")
            return
        print(
            f"ignored empty findings review for {repository}#{pr_number} "
            f"(head={head_sha}) — not evidence of CLEAN"
        )
        belt_ignored(
            "empty-findings-not-clean", pull_request=pr_number, head_sha=head_sha
        )
        return

    if review_round >= MAX_REVIEW_ROUNDS:
        counts = severity_counts(findings)
        locations = ", ".join(
            f"{finding.get('path', '?')}:{finding.get('line', '?')}"
            for finding in findings[:10]
        )
        if len(findings) > 10:
            locations += f", and {len(findings) - 10} more"
        reason = (
            f"Codex still reports {counts['total']} finding(s) on the exact "
            f"current head ({counts['p1']} P1 / {counts['p2']} P2 / "
            f"{counts['p3']} P3). Locations: {locations}."
        )
        gate = exhaustion_gate(
            pr_url=pr_url,
            head_sha=head_sha,
            reviewed_heads=review_round,
            reason=reason,
        )
        comment_state = ensure_exhaustion_gate_at_head(
            github,
            pr_number,
            gate,
            head_sha=head_sha,
            repository=repository,
            action="exhaustion gate",
        )
        if comment_state not in COMMENT_AT_HEAD_PUBLISHED:
            print(
                f"ignored exhaustion gate for {repository}#{pr_number} "
                f"(head={head_sha}): {comment_state}"
            )
            belt_ignored(comment_state, pull_request=pr_number, head_sha=head_sha)
            return
        if comment_state == "existing":
            print(
                f"exhaustion gate already present for "
                f"{repository}#{pr_number} (head={head_sha}); retrying wake"
            )
        # The gate comment is durable and already posted, so a later scheduled
        # scan returns early on it: these two spans are recorded before the
        # fallible wake because a Slack failure here would otherwise erase an
        # exhaustion that really happened, with no path back to it.
        belt_verdict(
            pr_number=pr_number,
            head_sha=head_sha,
            verdict_kind="findings",
            decision="exhaustion_gate",
            source_event_at=review.get("submitted_at"),
            review_round=review_round,
            rounds_consumed=len(reviewed_heads),
            counts=counts,
            findings=findings,
            author_seat=author_actor,
            review_state=review_state,
            base_ref=base_ref,
            base_sha=base_sha,
            head_commit_age=belt().head_commit_age_seconds(github, head_sha),
        )
        belt().event(
            "belt.exhaustion",
            **{
                "logfire.msg": (
                    f"#{pr_number} exhausted at round "
                    f"{review_round}/{MAX_REVIEW_ROUNDS}"
                ),
                "pull_request": pr_number,
                "head_sha": head_sha,
                "round": review_round,
                "max_review_rounds": MAX_REVIEW_ROUNDS,
                "gate_comment_state": comment_state,
                "findings_total": counts["total"],
                "author_seat": author_actor,
            },
        )
        if not deliver_wake(
            lambda: slack.post_message(
                f"WAKE: {author_actor}\n\n"
                f"Review-loop hook: automatic repair/re-review exhausted at round "
                f"{review_round}/{MAX_REVIEW_ROUNDS}. Do not burn or merge "
                "automatically.\n\n"
                f"{gate}"
            ),
            github=github,
            repository=repository,
            pr_number=pr_number,
            head_sha=head_sha,
            decision="exhaustion_gate",
        ):
            return
        print(
            f"review loop exhausted for {repository}#{pr_number} "
            f"(head={head_sha}, findings={len(findings)})"
        )
        # The gate comment and the authoring-seat wake are already published:
        # the retrospective is a third message that never gates or delays them,
        # and a failure here terminalizes visibly instead of being swallowed.
        head_bases = recorded_head_bases(conversation_comments)
        head_bases.setdefault(head_sha, base_sha)
        history = round_history(
            reviewed_heads,
            [*reviews, review],
            review_comments,
            codex_login,
            latest_results=latest_result_by_head(result_events),
            head_bases=head_bases,
            issue_comments=conversation_comments,
        )
        deliver_wake(
            lambda: publish_exhaustion_retrospective(
                slack,
                github=github,
                findings=findings,
                history=history,
                pr_url=pr_url,
                branch=branch,
                head_sha=head_sha,
                base_ref=base_ref,
                base_sha=base_sha,
                repository=repository,
                author=author,
                author_actor=author_actor,
                review_round=review_round,
                pr_number=pr_number,
            ),
            github=github,
            repository=repository,
            pr_number=pr_number,
            head_sha=head_sha,
            decision="exhaustion_retrospective",
        )
        return

    history = round_history(
        reviewed_heads,
        [*reviews, review],
        review_comments,
        codex_login,
        latest_results=latest_result_by_head(result_events),
        issue_comments=conversation_comments,
    )
    cast = burn_cast()
    messages = build_burn_messages(
        findings=findings,
        review_state=review_state,
        pr_url=pr_url,
        branch=branch,
        head_sha=head_sha,
        base_ref=base_ref,
        base_sha=base_sha,
        repository=repository,
        author=author,
        author_actor=author_actor,
        review_round=review_round,
        history=history,
        cast=cast,
        effort=burn_effort(pr_labels(pr_state)),
    )
    belt_verdict(
        pr_number=pr_number,
        head_sha=head_sha,
        verdict_kind="findings",
        decision="burn_wake",
        source_event_at=review.get("submitted_at"),
        review_round=review_round,
        rounds_consumed=len(reviewed_heads),
        counts=severity_counts(findings),
        findings=findings,
        author_seat=author_actor,
        review_state=review_state,
        base_ref=base_ref,
        base_sha=base_sha,
        chunks=len(messages),
        head_commit_age=belt().head_commit_age_seconds(github, head_sha),
    )
    if deliver_wake(
        lambda: post_threaded_messages(
            slack,
            messages,
            github=github,
            repository=repository,
            pr_number=pr_number,
            head_sha=head_sha,
            decision="burn_wake",
        ),
        github=github,
        repository=repository,
        pr_number=pr_number,
        head_sha=head_sha,
        decision="burn_wake",
        chunks=len(messages),
    ):
        print(
            f"woke {cast[0]} for {repository}#{pr_number} "
            f"(findings={len(findings)}, author={author_actor}, "
            f"messages={len(messages)})"
        )


def unroutable_comment_message(
    *,
    kind: str,
    pr_url: str,
    comment_url: str,
    reference: str | None,
    first_line: str,
) -> str:
    anchor = f"`{reference}`" if reference else "none it could pin"
    return (
        "FYI: review-loop saw a Codex comment it cannot route.\n"
        f"PR: {pr_url}\n"
        f"Comment: {comment_url}\n"
        f"Shape: `{kind}`  |  commit reference: {anchor}\n"
        f"First line: `{first_line}`\n"
        "No verdict was recorded for that head, so the bounded loop still "
        "treats it as unreviewed. If this is a verdict format, teach "
        "`codex_comment_kind` to recognise it."
    )


def report_unroutable_codex_comment(
    comment: Mapping[str, Any],
    codex_login: str,
    repository: str,
    issue: Mapping[str, Any],
) -> None:
    """Say out loud that a Codex comment carried a verdict the loop cannot use.

    Two tickets were paid for the opposite behaviour: an unrecognised verdict
    format was dropped in silence, and the only symptom was a head that never
    closed.  Known non-verdict shapes stay quiet; anything that looks like a
    verdict reaches #hive — a clean assertion with no pinnable head, a
    task-channel verdict that is not clean (whether or not it pins a commit:
    its findings have no route at all), or an unrecognised shape that still
    points at a commit.
    """
    user = comment.get("user")
    if not isinstance(user, Mapping) or user.get("login") != codex_login:
        print("ignored comment from a non-Codex author")
        return
    body = str(comment.get("body") or "")
    kind = codex_comment_kind(body)
    if kind == CODEX_COMMENT_QUOTA_REFUSAL:
        belt().event(
            "belt.refusal.observed",
            **{
                "logfire.msg": "Codex quota refusal observed on a comment",
                "channel": "comment",
                "pull_request": int(issue.get("number") or 0),
            },
        )
        # The refusal is the moment the find half went down for this head.
        # The scheduled scan reaches the same conclusion up to the stall
        # threshold plus one cron tick later; routing the event through the
        # same per-PR reconciliation (stall gate off — Codex has refused,
        # there is nothing left to wait for) removes that latency without a
        # second routing policy.
        summon_on_refusal(issue, repository)
        return
    if kind in (
        CODEX_COMMENT_TASK_REPORT,
        CODEX_COMMENT_CONNECTOR_ERROR,
    ):
        print(f"ignored Codex {kind} comment")
        return
    reference = comment_commit_reference(body, repository)
    if kind == CODEX_COMMENT_UNKNOWN and reference is None:
        print("ignored unrecognised Codex comment with no commit reference")
        return

    pr_number = issue.get("number")
    slack = SlackApi(required_env("HIVE_BOT_TOKEN"), required_env("HIVE_CHANNEL"))
    slack.post_message(
        unroutable_comment_message(
            kind=kind,
            pr_url=str(issue.get("html_url") or f"{repository}#{pr_number}"),
            comment_url=str(comment.get("html_url") or "unknown"),
            reference=reference,
            first_line=body.strip().splitlines()[0][:120] if body.strip() else "",
        )
    )
    print(f"reported unroutable Codex {kind} comment on {repository}#{pr_number}")
    belt().event(
        "belt.comment.unroutable",
        **{
            "logfire.msg": f"unroutable Codex {kind} comment",
            "comment_kind": kind,
            "pull_request": int(pr_number or 0),
        },
    )


def route_clean_comment(event: Mapping[str, Any] | None = None) -> None:
    """Route Codex's clean issue comment after resolving its exact reviewed SHA."""
    event = event or load_event()
    comment = event.get("comment")
    issue = event.get("issue")
    if not isinstance(comment, Mapping) or not isinstance(issue, Mapping):
        raise TypeError("event does not contain a comment and issue")
    if not isinstance(issue.get("pull_request"), Mapping):
        print("ignored non-PR issue comment")
        return

    codex_login = os.environ.get("CODEX_LOGIN", CODEX_LOGIN)
    repository = required_env("GITHUB_REPOSITORY")
    if clean_comment_commitish(comment, codex_login, repository) is None:
        report_unroutable_codex_comment(comment, codex_login, repository, issue)
        return

    github = GitHubApi(required_env("GITHUB_TOKEN"), repository)
    reviewed_head = clean_comment_head(github, comment, codex_login)
    if reviewed_head is None:
        print("ignored unresolvable Codex clean comment")
        belt_ignored(
            "unresolvable-clean-comment",
            pull_request=int(issue.get("number") or 0),
        )
        return

    pr_number = int(issue["number"])
    pr_state = github.get(f"pulls/{pr_number}")
    if not isinstance(pr_state, Mapping):
        raise TypeError("pull request lookup did not return an object")
    head = pr_state.get("head")
    if not isinstance(head, Mapping):
        raise TypeError("live pull_request.head is missing")
    head_sha = str(head["sha"])
    if reviewed_head != head_sha.lower():
        print(
            f"ignored stale Codex clean comment for {repository}#{pr_number} "
            f"(review={reviewed_head}, current={head_sha})"
        )
        belt_ignored(
            "stale-verdict-head",
            pull_request=pr_number,
            head_sha=head_sha,
            verdict_head=reviewed_head,
        )
        return

    resolved = author_for_pr(github, pr_number, head_sha, pr_state)
    if resolved is None:
        print("non-seat author - no wake")
        belt_ignored("non-seat-author", pull_request=pr_number, head_sha=head_sha)
        return
    author, author_actor = resolved
    if loop_exempt_pr(github, pr_number):
        print(
            f"loop-exempt PR {repository}#{pr_number} - every touched path "
            "sits under a corpus root with its own gate; no wake"
        )
        belt_ignored("loop-exempt-pr", pull_request=pr_number, head_sha=head_sha)
        return
    reviews = github.paginate(f"pulls/{pr_number}/reviews")
    conversation_comments = github.paginate(f"issues/{pr_number}/comments")
    reviewed_heads = codex_result_heads(
        github,
        reviews,
        [*conversation_comments, comment],
        codex_login,
        pr_number=pr_number,
    )
    review_round = result_round_for_head(reviewed_heads, head_sha)
    refreshed_pr = refresh_pr_at_head(
        github,
        pr_number,
        head_sha,
        repository,
        on_ignored=lambda reason: belt_ignored(
            reason, pull_request=pr_number, head_sha=head_sha
        ),
    )
    if refreshed_pr is None:
        return
    pr_state = refreshed_pr
    refreshed_head = pr_state.get("head")
    assert isinstance(refreshed_head, Mapping)
    branch = str(refreshed_head["ref"])
    pr_url = str(pr_state.get("html_url") or issue.get("html_url") or "")
    base_ref, base_sha = pr_base(pr_state)
    pin_state = record_reviewed_head_base(
        github,
        pr_number,
        head_sha,
        base_ref,
        base_sha,
        repository=repository,
        comments=conversation_comments,
    )
    if pin_state not in COMMENT_AT_HEAD_PUBLISHED:
        belt_ignored(pin_state, pull_request=pr_number, head_sha=head_sha)
        return
    stale_ref = stale_base_ref_for_closure(conversation_comments, head_sha, base_ref)
    if stale_ref is not None:
        print(
            f"refused clean closure for {repository}#{pr_number}: head "
            f"{head_sha} was reviewed against base ref `{stale_ref}` but the "
            f"PR now targets `{base_ref}` — the head SHA alone no longer "
            "names the reviewed subject; resolve the retarget and request a "
            "fresh exact-head review"
        )
        belt().event(
            "belt.closure.refused",
            **{
                "logfire.msg": "clean closure refused: stale-base-ref",
                "reason": "stale-base-ref",
                "pull_request": pr_number,
                "head_sha": head_sha,
                "base_ref": base_ref,
            },
        )
        return
    retargeted_at = base_retarget_after(
        github, pr_number, str(comment.get("created_at") or "")
    )
    if retargeted_at is not None:
        print(
            f"refused clean closure for {repository}#{pr_number}: the PR base "
            f"was retargeted at `{retargeted_at}`, after this verdict was "
            "formed — the review's subject is not the PR as now targeted; "
            "request a fresh exact-head review"
        )
        belt().event(
            "belt.closure.refused",
            **{
                "logfire.msg": "clean closure refused: base-retargeted",
                "reason": "base-retargeted",
                "pull_request": pr_number,
                "head_sha": head_sha,
                "base_ref": base_ref,
            },
        )
        return
    slack = SlackApi(required_env("HIVE_BOT_TOKEN"), required_env("HIVE_CHANNEL"))
    belt_verdict(
        pr_number=pr_number,
        head_sha=head_sha,
        verdict_kind="clean",
        decision="clean_wake",
        source_event_at=comment.get("created_at"),
        review_round=review_round,
        rounds_consumed=len(reviewed_heads),
        author_seat=author_actor,
        review_state="clean-comment",
        base_ref=base_ref,
        base_sha=base_sha,
        head_commit_age=belt().head_commit_age_seconds(github, head_sha),
    )
    if deliver_wake(
        lambda: slack.post_message(
            clean_wake_message(
                author_actor=author_actor,
                author=author,
                head_sha=head_sha,
                review_round=review_round,
                review_state="clean-comment",
                pr_url=pr_url,
                branch=branch,
            )
        ),
        github=github,
        repository=repository,
        pr_number=pr_number,
        head_sha=head_sha,
        decision="clean_wake",
    ):
        print(f"woke {author_actor} for {repository}#{pr_number} (clean comment)")


def route_substitute_verdict(event: Mapping[str, Any]) -> None:
    """Route a trusted substitute reviewer's exact-head verdict, both kinds.

    CLEAN wakes the authoring seat exactly like a Codex CLEAN.  FINDINGS
    dispatches the burn twin exactly like a Codex findings review — counts
    from the marker, the digest being the substitute's verdict comment
    verbatim (seat prose is never re-parsed into structure).  A findings
    verdict that neither burns nor gates is a black hole: the head counts as
    reviewed while the burn twin never learns the findings exist.  A marker
    from an untrusted author is a forgery and routes nothing.
    """
    comment = event.get("comment")
    issue = event.get("issue")
    if not isinstance(comment, Mapping) or not isinstance(issue, Mapping):
        raise TypeError("event does not contain a comment and issue")
    if not isinstance(issue.get("pull_request"), Mapping):
        print("ignored non-PR substitute verdict comment")
        return
    parsed = substitute_verdicts([comment])
    if not parsed:
        author = comment.get("user")
        login = author.get("login") if isinstance(author, Mapping) else "unknown"
        print(f"ignored substitute-verdict marker from untrusted author {login}")
        belt_ignored(
            "untrusted-substitute-marker",
            pull_request=int(issue.get("number") or 0),
        )
        return
    _, verdict = parsed[0]
    repository = required_env("GITHUB_REPOSITORY")
    pr_number = int(issue["number"])
    github = GitHubApi(required_env("GITHUB_TOKEN"), repository)
    pr_state = github.get(f"pulls/{pr_number}")
    if not isinstance(pr_state, Mapping):
        raise TypeError("pull request lookup did not return an object")
    head = pr_state.get("head")
    if not isinstance(head, Mapping):
        raise TypeError("live pull_request.head is missing")
    head_sha = str(head["sha"])
    if verdict["head"] != head_sha.lower():
        print(
            f"ignored stale substitute {verdict['kind']} verdict for "
            f"{repository}#{pr_number} "
            f"(verdict={verdict['head']}, current={head_sha})"
        )
        belt_ignored(
            "stale-verdict-head",
            pull_request=pr_number,
            head_sha=head_sha,
            verdict_head=str(verdict["head"]),
            substitute_actor=str(verdict["actor"]),
        )
        return

    resolved = author_for_pr(github, pr_number, head_sha, pr_state)
    if resolved is None:
        print("non-seat author - no wake")
        belt_ignored("non-seat-author", pull_request=pr_number, head_sha=head_sha)
        return
    author, author_actor = resolved
    if loop_exempt_pr(github, pr_number):
        print(
            f"loop-exempt PR {repository}#{pr_number} - every touched path "
            "sits under a corpus root with its own gate; no wake"
        )
        belt_ignored("loop-exempt-pr", pull_request=pr_number, head_sha=head_sha)
        return
    codex_login = os.environ.get("CODEX_LOGIN", CODEX_LOGIN)
    reviews = github.paginate(f"pulls/{pr_number}/reviews")
    conversation_comments = github.paginate(f"issues/{pr_number}/comments")
    reviewed_heads = codex_result_heads(
        github,
        reviews,
        [*conversation_comments, comment],
        codex_login,
        pr_number=pr_number,
    )
    review_round = result_round_for_head(reviewed_heads, head_sha.lower())
    refreshed_pr = refresh_pr_at_head(
        github,
        pr_number,
        head_sha,
        repository,
        on_ignored=lambda reason: belt_ignored(
            reason, pull_request=pr_number, head_sha=head_sha
        ),
    )
    if refreshed_pr is None:
        return
    pr_state = refreshed_pr
    refreshed_head = pr_state.get("head")
    assert isinstance(refreshed_head, Mapping)
    branch = str(refreshed_head["ref"])
    pr_url = str(pr_state.get("html_url") or issue.get("html_url") or "")
    base_ref, base_sha = pr_base(pr_state)
    pin_state = record_reviewed_head_base(
        github,
        pr_number,
        head_sha,
        base_ref,
        base_sha,
        repository=repository,
        comments=conversation_comments,
    )
    if pin_state not in COMMENT_AT_HEAD_PUBLISHED:
        belt_ignored(pin_state, pull_request=pr_number, head_sha=head_sha)
        return
    slack = SlackApi(required_env("HIVE_BOT_TOKEN"), required_env("HIVE_CHANNEL"))
    if verdict["kind"] != "clean":
        if review_round >= MAX_REVIEW_ROUNDS:
            # The automatic loop is exhausted. The scan CANNOT own this gate:
            # this verdict already entered the result stream, so the head is
            # in reviewed_heads and the scan's exhaustion post is behind
            # `head_sha not in reviewed_heads` — deferring here was the same
            # black hole one bound later. Mirror route_review: gate comment,
            # authoring-seat wake, Theoros retrospective. Counts come from
            # the marker (the inline list is empty by construction).
            counts = verdict["counts"]
            total = counts["p1"] + counts["p2"] + counts["p3"]
            reason = (
                f"Substitute ({verdict['actor']}) still reports {total} "
                f"finding(s) on the exact current head ({counts['p1']} P1 / "
                f"{counts['p2']} P2 / {counts['p3']} P3, marker counts). "
                "The digest is the substitute's verdict comment on the PR."
            )
            gate = exhaustion_gate(
                pr_url=pr_url,
                head_sha=head_sha,
                reviewed_heads=review_round,
                reason=reason,
            )
            comment_state = ensure_comment_at_head(
                github,
                pr_number,
                exhaustion_marker(head_sha),
                gate,
                expected_head=head_sha,
                repository=repository,
                action="exhaustion gate",
            )
            if comment_state not in COMMENT_AT_HEAD_PUBLISHED:
                print(
                    f"ignored substitute exhaustion gate for "
                    f"{repository}#{pr_number} (head={head_sha}): "
                    f"{comment_state}"
                )
                belt_ignored(comment_state, pull_request=pr_number, head_sha=head_sha)
                return
            if comment_state == "existing":
                print(
                    f"exhaustion gate already present for "
                    f"{repository}#{pr_number} (head={head_sha}); retrying wake"
                )
            # Recorded before the fallible wake, for the reason the Codex
            # exhaustion branch states: the gate comment is durable, so a
            # later scan returns early and never rebuilds these spans.
            belt_verdict(
                pr_number=pr_number,
                head_sha=head_sha,
                verdict_kind="substitute-findings",
                decision="exhaustion_gate",
                source_event_at=comment.get("created_at"),
                review_round=review_round,
                rounds_consumed=len(reviewed_heads),
                counts={**counts, "total": total},
                author_seat=author_actor,
                review_state=f"substitute-findings:{verdict['actor']}",
                base_ref=base_ref,
                base_sha=base_sha,
                substitute=str(verdict["actor"]),
                head_commit_age=belt().head_commit_age_seconds(github, head_sha),
            )
            belt().event(
                "belt.exhaustion",
                **{
                    "logfire.msg": (
                        f"#{pr_number} exhausted at round "
                        f"{review_round}/{MAX_REVIEW_ROUNDS} (substitute)"
                    ),
                    "pull_request": pr_number,
                    "head_sha": head_sha,
                    "round": review_round,
                    "max_review_rounds": MAX_REVIEW_ROUNDS,
                    "gate_comment_state": comment_state,
                    "findings_total": total,
                    "author_seat": author_actor,
                    "substitute_actor": str(verdict["actor"]),
                },
            )
            if not deliver_wake(
                lambda: slack.post_message(
                    f"WAKE: {author_actor}\n\n"
                    f"Review-loop hook: automatic repair/re-review exhausted at "
                    f"round {review_round}/{MAX_REVIEW_ROUNDS} (substitute "
                    f"verdict by `{verdict['actor']}`). Do not burn or merge "
                    "automatically.\n\n"
                    f"{gate}"
                ),
                github=github,
                repository=repository,
                pr_number=pr_number,
                head_sha=head_sha,
                decision="exhaustion_gate",
            ):
                return
            print(
                f"review loop exhausted for {repository}#{pr_number} "
                f"(head={head_sha}, substitute findings={total})"
            )
            review_comments = github.paginate(f"pulls/{pr_number}/comments")
            head_bases = recorded_head_bases(conversation_comments)
            head_bases.setdefault(head_sha, base_sha)
            history = round_history(
                reviewed_heads,
                reviews,
                review_comments,
                codex_login,
                latest_results=latest_result_by_head(
                    codex_result_events(
                        github,
                        reviews,
                        [*conversation_comments, comment],
                        codex_login,
                        pr_number=pr_number,
                        review_comments=review_comments,
                    )
                ),
                head_bases=head_bases,
                issue_comments=[*conversation_comments, comment],
            )
            deliver_wake(
                lambda: publish_exhaustion_retrospective(
                    slack,
                    github=github,
                    findings=[],
                    history=history,
                    pr_url=pr_url,
                    branch=branch,
                    head_sha=head_sha,
                    base_ref=base_ref,
                    base_sha=base_sha,
                    repository=repository,
                    author=author,
                    author_actor=author_actor,
                    review_round=review_round,
                    pr_number=pr_number,
                    substitute={
                        "actor": verdict["actor"],
                        "counts": verdict["counts"],
                        "body": str(comment.get("body") or ""),
                    },
                ),
                github=github,
                repository=repository,
                pr_number=pr_number,
                head_sha=head_sha,
                decision="exhaustion_retrospective",
            )
            return
        review_comments = github.paginate(f"pulls/{pr_number}/comments")
        history = round_history(
            reviewed_heads,
            reviews,
            review_comments,
            codex_login,
            latest_results=latest_result_by_head(
                codex_result_events(
                    github,
                    reviews,
                    [*conversation_comments, comment],
                    codex_login,
                    pr_number=pr_number,
                    review_comments=review_comments,
                )
            ),
            issue_comments=[*conversation_comments, comment],
        )
        cast = burn_cast()
        messages = build_burn_messages(
            findings=[],
            review_state=f"substitute-findings:{verdict['actor']}",
            pr_url=pr_url,
            branch=branch,
            head_sha=head_sha,
            base_ref=base_ref,
            base_sha=base_sha,
            repository=repository,
            author=author,
            author_actor=author_actor,
            review_round=review_round,
            history=history,
            substitute={
                "actor": verdict["actor"],
                "counts": verdict["counts"],
                "body": str(comment.get("body") or ""),
            },
            cast=cast,
            effort=burn_effort(pr_labels(pr_state)),
        )
        counts = verdict["counts"]
        belt_verdict(
            pr_number=pr_number,
            head_sha=head_sha,
            verdict_kind="substitute-findings",
            decision="burn_wake",
            source_event_at=comment.get("created_at"),
            review_round=review_round,
            rounds_consumed=len(reviewed_heads),
            counts={
                **counts,
                "total": counts["p1"] + counts["p2"] + counts["p3"],
            },
            author_seat=author_actor,
            review_state=f"substitute-findings:{verdict['actor']}",
            base_ref=base_ref,
            base_sha=base_sha,
            chunks=len(messages),
            substitute=str(verdict["actor"]),
            head_commit_age=belt().head_commit_age_seconds(github, head_sha),
        )
        if deliver_wake(
            lambda: post_threaded_messages(
                slack,
                messages,
                github=github,
                repository=repository,
                pr_number=pr_number,
                head_sha=head_sha,
                decision="burn_wake",
            ),
            github=github,
            repository=repository,
            pr_number=pr_number,
            head_sha=head_sha,
            decision="burn_wake",
            chunks=len(messages),
        ):
            print(
                f"woke {cast[0]} for {repository}#{pr_number} "
                f"(substitute findings by {verdict['actor']}, "
                f"counts={verdict['counts']}, messages={len(messages)})"
            )
        return
    stale_ref = stale_base_ref_for_closure(conversation_comments, head_sha, base_ref)
    if stale_ref is not None:
        print(
            f"refused substitute clean closure for {repository}#{pr_number}: "
            f"head {head_sha} was reviewed against base ref `{stale_ref}` but "
            f"the PR now targets `{base_ref}` — the head SHA alone no longer "
            "names the reviewed subject; resolve the retarget and request a "
            "fresh exact-head review"
        )
        belt().event(
            "belt.closure.refused",
            **{
                "logfire.msg": "clean closure refused: stale-base-ref",
                "reason": "stale-base-ref",
                "pull_request": pr_number,
                "head_sha": head_sha,
                "base_ref": base_ref,
            },
        )
        return
    retargeted_at = base_retarget_after(
        github, pr_number, str(comment.get("created_at") or "")
    )
    if retargeted_at is not None:
        print(
            f"refused substitute clean closure for {repository}#{pr_number}: "
            f"the PR base was retargeted at `{retargeted_at}`, after this "
            "verdict was formed — the review's subject is not the PR as now "
            "targeted; request a fresh exact-head review"
        )
        belt().event(
            "belt.closure.refused",
            **{
                "logfire.msg": "clean closure refused: base-retargeted",
                "reason": "base-retargeted",
                "pull_request": pr_number,
                "head_sha": head_sha,
                "base_ref": base_ref,
            },
        )
        return
    belt_verdict(
        pr_number=pr_number,
        head_sha=head_sha,
        verdict_kind="substitute-clean",
        decision="clean_wake",
        source_event_at=comment.get("created_at"),
        review_round=review_round,
        rounds_consumed=len(reviewed_heads),
        author_seat=author_actor,
        review_state=f"substitute-clean:{verdict['actor']}",
        base_ref=base_ref,
        base_sha=base_sha,
        substitute=str(verdict["actor"]),
        head_commit_age=belt().head_commit_age_seconds(github, head_sha),
    )
    if deliver_wake(
        lambda: slack.post_message(
            clean_wake_message(
                author_actor=author_actor,
                author=author,
                head_sha=head_sha,
                review_round=review_round,
                review_state=f"substitute-clean:{verdict['actor']}",
                pr_url=pr_url,
                branch=branch,
                verdict_source=f"substitute review (`{verdict['actor']}`)",
            )
        ),
        github=github,
        repository=repository,
        pr_number=pr_number,
        head_sha=head_sha,
        decision="clean_wake",
    ):
        print(
            f"woke {author_actor} for {repository}#{pr_number} "
            f"(substitute clean by {verdict['actor']})"
        )


def summon_on_refusal(issue: Mapping[str, Any], repository: str) -> None:
    """Reconcile one PR immediately when Codex refuses it on quota."""
    if not issue.get("pull_request"):
        print("ignored quota refusal outside a pull request")
        return
    pr_number = int(issue.get("number") or 0)
    github = GitHubApi(required_env("GITHUB_TOKEN"), repository)
    pull_request = github.get(f"pulls/{pr_number}")
    if str(pull_request.get("state")) != "open":
        print(f"ignored quota refusal on non-open PR #{pr_number}")
        return
    codex_login = os.environ.get("CODEX_LOGIN", CODEX_LOGIN)
    nudged, summoned, redelivered, chased = _scan_open_pull(
        github,
        pull_request,
        repository=repository,
        codex_login=codex_login,
        now=datetime.now(timezone.utc),
        stall_gate=False,
    )
    print(
        f"refusal-routed PR #{pr_number} "
        f"(nudged={nudged}, summoned={summoned}, redelivered={redelivered}, "
        f"chased={chased})"
    )


def route_comment_event(event: Mapping[str, Any]) -> None:
    """Route one issue-comment event: substitute verdict, malformed marker,
    or the clean-comment path."""
    comment = event.get("comment")
    if not isinstance(comment, Mapping):
        raise TypeError("event does not contain a comment")
    codex_login = os.environ.get("CODEX_LOGIN", CODEX_LOGIN)
    user = comment.get("user")
    author = user.get("login") if isinstance(user, Mapping) else None
    marker_state = substitute_verdict_marker_state([comment])
    if author != codex_login and marker_state == "present":
        route_substitute_verdict(event)
        return
    if (
        author != codex_login
        and author in trusted_control_logins()
        and marker_state == "malformed"
    ):
        # A trusted substitute tried to post a verdict and the marker
        # does not parse. Falling through to the clean-comment path
        # ignores it silently while the standing summon marker suppresses
        # every scheduled retry — a permanently unreviewed head. R-3:
        # terminalize loudly so the malformed verdict is visible and the
        # substitute can repost the marker verbatim. (Summon comments
        # quote the marker grammar and are excluded by their own marker.)
        raise RuntimeError(
            "trusted substitute verdict marker does not parse "
            f"(author={author}); repost the verdict with the marker "
            "grammar quoted in the summon, verbatim"
        )
    route_clean_comment(event)


def route_codex_result() -> None:
    """Route Codex's findings review, its clean comment, or a substitute verdict."""
    event = load_event()
    if isinstance(event.get("review"), Mapping):
        route_review(event)
        return
    if isinstance(event.get("comment"), Mapping):
        route_comment_event(event)
        return
    raise TypeError("event contains neither a review nor an issue comment")


def parse_github_time(value: str) -> datetime:
    return datetime.fromisoformat(value.replace("Z", "+00:00"))


def result_event_time(raw: Any) -> datetime:
    """Parse a GitHub event timestamp; undated events sort first, then by input order."""
    if not isinstance(raw, str) or not raw.strip():
        return datetime.min.replace(tzinfo=timezone.utc)
    try:
        parsed = parse_github_time(raw.strip())
    except ValueError:
        return datetime.min.replace(tzinfo=timezone.utc)
    if parsed.tzinfo is None:
        return parsed.replace(tzinfo=timezone.utc)
    return parsed


def commit_time(commit: Mapping[str, Any], fallback: str) -> datetime:
    nested = commit.get("commit")
    if isinstance(nested, Mapping):
        for role in ("committer", "author"):
            identity = nested.get(role)
            if isinstance(identity, Mapping) and identity.get("date"):
                return parse_github_time(str(identity["date"]))
    return parse_github_time(fallback)


def review_stall_anchor(
    commit: Mapping[str, Any], pull_request: Mapping[str, Any], now: datetime
) -> datetime:
    """Use a stable server timestamp when the client-authored commit date is future.

    GitHub preserves author-controlled commit timestamps. A bad agent clock must
    not suppress nudges indefinitely, but it also must not bypass the ordinary
    20-minute review window. Fall back to the PR's server-observed update (or
    creation) time for an implausible future commit date.
    """
    fallback = str(pull_request["created_at"])
    committed_at = commit_time(commit, fallback)
    if committed_at <= now:
        return committed_at
    server_observed = str(pull_request.get("updated_at") or fallback)
    return parse_github_time(server_observed)


def bare_nudge_covers_head(
    comments: Sequence[Mapping[str, Any]],
    head_sha: str,
) -> bool:
    """True when a prior control-identity nudge already targeted this exact head.

    Timestamps are not used: a force-push or reset onto an older commit can make
    an earlier head's nudge ``created_at`` fall after the restored head's
    committer date, which would falsely suppress re-nudges for the current SHA.
    Marker text alone is not enough — only a trusted control identity counts.
    """
    return marker_comment_exists(comments, nudge_marker_pattern(head_sha))


def exact_head_codex_reviews(
    reviews: Sequence[Mapping[str, Any]], head_sha: str, codex_login: str
) -> list[Mapping[str, Any]]:
    """Codex reviews submitted against this exact head, in review order."""
    wanted = head_sha.lower()
    matched: list[Mapping[str, Any]] = []
    for review in reviews:
        user = review.get("user")
        if not isinstance(user, Mapping) or user.get("login") != codex_login:
            continue
        if is_quota_refusal_body(str(review.get("body") or "")):
            continue
        if str(review.get("commit_id") or "").strip().lower() == wanted:
            matched.append(review)
    return matched


def standing_verdict_time(
    github: GitHubApi,
    reviews: Sequence[Mapping[str, Any]],
    comments: Sequence[Mapping[str, Any]],
    head_sha: str,
    codex_login: str,
) -> datetime | None:
    """When Codex last published a verdict for this exact head.

    Both verdict channels count: a submitted review's ``submitted_at`` and a
    clean comment's ``created_at``.  The *latest* is the anchor — the window
    measures how long the current verdict has stood unacted, so a re-review
    restarts it rather than inheriting the first delivery's age.
    """
    stamps: list[datetime] = []
    for review in exact_head_codex_reviews(reviews, head_sha, codex_login):
        submitted = str(review.get("submitted_at") or "").strip()
        if submitted:
            stamps.append(parse_github_time(submitted))
    for comment in comments:
        created = str(comment.get("created_at") or "").strip()
        if not created:
            continue
        if clean_comment_head(github, comment, codex_login) == head_sha.lower():
            stamps.append(parse_github_time(created))
    for _, verdict in substitute_verdicts(comments):
        if verdict["head"] == head_sha.lower():
            stamps.append(verdict["at"])
    return max(stamps) if stamps else None


def standing_findings(
    github: GitHubApi,
    pr_number: int,
    reviews: Sequence[Mapping[str, Any]],
    codex_login: str,
) -> list[dict[str, Any]]:
    """Inline findings belonging to the supplied reviews.

    The caller chooses the review set.  Redelivery passes every same-head
    findings review since the most recent CLEAN: a later findings review
    does not resolve earlier comments, and only CLEAN (or a new head) does.
    Each inline comment belongs to exactly one review, so the result is a
    concatenation with no deduplication.  The comment list is fetched once
    and filtered per review, matching ``review_findings``'s contract.
    """
    review_comments = list(github.paginate(f"pulls/{pr_number}/comments"))
    findings: list[dict[str, Any]] = []
    for review in reviews:
        findings.extend(
            review_findings(review_comments, int(review["id"]), codex_login)
        )
    return findings


def same_head_findings_reviews_since_clean(
    reviews: Sequence[Mapping[str, Any]],
    result_events: Sequence[ResultEvent],
    head_sha: str,
    codex_login: str,
) -> list[Mapping[str, Any]]:
    """Exact-head findings reviews still standing after the latest CLEAN.

    A later findings review does not resolve earlier comments on the same SHA.
    Only a CLEAN verdict (or a new head) does.  Reviews submitted at or before
    the latest CLEAN on this head are dropped; everything after it is kept.
    """
    wanted = head_sha.lower()
    last_clean_at: datetime | None = None
    for at, _order, head, kind, _source, _identity in result_events:
        if kind == "clean" and str(head).lower() == wanted:
            last_clean_at = at
    standing: list[Mapping[str, Any]] = []
    for review in exact_head_codex_reviews(reviews, head_sha, codex_login):
        if (
            last_clean_at is not None
            and result_event_time(review.get("submitted_at")) <= last_clean_at
        ):
            continue
        standing.append(review)
    return standing


def latest_exact_head_review(
    reviews: Sequence[Mapping[str, Any]], head_sha: str, codex_login: str
) -> Mapping[str, Any] | None:
    """The latest Codex review submitted against this exact head."""
    exact = exact_head_codex_reviews(reviews, head_sha, codex_login)
    if not exact:
        return None
    indexed = list(enumerate(exact))
    return max(
        indexed,
        key=lambda item: (result_event_time(item[1].get("submitted_at")), item[0]),
    )[1]


def retrospective_chase_wake_message(
    *,
    pr_url: str,
    pr_number: int,
    repository: str,
    head_sha: str,
    requested_at: datetime,
    pr_state: str = "open",
    actor: str = RETROSPECTIVE_ACTOR,
) -> str:
    """Re-ask for a requested retrospective that never reached the PR.

    A pointer, not a second digest: the evidence was delivered once and the
    thread still holds it.  Re-sending the per-round history would make this
    look like a fresh dispatch, and it is not — no new round, no repair
    authority, no merge authority, and no reviewer is summoned.

    A chase can reach a seat after the PR has been closed or merged, because
    closure inside the delivery window is a normal outcome.  The wake says so
    where that is true: the testimony is still owed and still historical, but a
    seat that has to derive the closure from the PR itself has spent a wake
    finding out what this line could have told it.
    """
    stamp = requested_at.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    state_line = (
        ""
        if pr_state == "open"
        else (
            f"State: `{pr_state}` — the PR is no longer open. The retrospective "
            "is testimony about a finished sequence: still owed, still gating "
            "nothing, and the closure is not yours to revisit.\n"
        )
    )
    return (
        f"WAKE: {actor}\n\n"
        "Review-loop hook: an exhaustion retrospective was requested from you "
        f"at `{stamp}` and no verdict has reached the PR. This is a "
        "redelivery of that one request, not a second one: it carries no "
        "repair, re-review or merge authority, and it adds no review round.\n\n"
        f"PR: {pr_url}\n"
        f"Head: `{head_sha}`\n"
        f"Repo: `{repository}`\n"
        f"{state_line}\n"
        "The original wake and its per-round evidence are in this thread's "
        "history, above; the exhaustion gate and the request receipt are on "
        "the PR. If you already wrote the verdict, it is on a disk and not "
        "here — post the file:\n\n"
        f"    gh pr comment {pr_number} -R {repository} --body-file <path>\n\n"
        "`--body @<path>` posts the literal string `@<path>`; `gh` has no "
        "`@file` idiom. End the body with exactly:\n\n"
        f"    {retrospective_marker(head_sha)}\n\n"
        "Silence is a legitimate verdict, but it is not a legitimate "
        "delivery: if there is nothing that generalises, post that finding "
        "with the marker. One more miss and the gap is stated on the PR."
    )


def retrospective_chase_comment_body(
    head_sha: str, attempt: int, actor: str = RETROSPECTIVE_ACTOR
) -> str:
    """The durable record of one chase; attempt ``RETROSPECTIVE_CHASE_ATTEMPTS`` names the gap.

    The last attempt is deliberately the loud one (R-3): a retrospective that
    was asked for and never arrived is a failure of the loop's third hook, and
    a failure nobody can see from the evidence is the defect this whole leg
    exists to close.  Two attempts, then it is a human's — automation that
    keeps asking is not persistence.
    """
    if attempt < RETROSPECTIVE_CHASE_ATTEMPTS:
        return (
            "Review-loop: the exhaustion retrospective requested for head "
            f"`{head_sha}` has not been posted here; `{actor}` "
            f"was re-woken once (attempt {attempt} of "
            f"{RETROSPECTIVE_CHASE_ATTEMPTS}). Attention only — no review "
            "round, no repair authority, no merge authority.\n"
            f"{retrospective_chase_marker(head_sha, attempt)}"
        )
    return (
        "## Exhaustion retrospective not delivered\n\n"
        f"The review loop asked `{actor}` for a structural "
        f"retrospective on head `{head_sha}` and re-asked once. No verdict "
        "carrying the retrospective marker has reached this PR, so the "
        "testimony behind this PR's exhaustion is unrecorded on the evidence "
        "it concerns.\n\n"
        f"Automation stops here: {RETROSPECTIVE_CHASE_ATTEMPTS} attempts is "
        "the bound, and a third would be repetition rather than persistence. "
        "This changes nothing about the PR — the retrospective never gated, "
        "repaired, re-reviewed or merged anything, and the human gate above "
        "still stands on its own. It is a human's call whether the verdict is "
        "still owed.\n"
        f"{retrospective_chase_marker(head_sha, attempt)}"
    )


def chase_undelivered_retrospective(
    github: GitHubApi,
    *,
    pr_number: int,
    pr_url: str,
    head_sha: str,
    comments: Sequence[Mapping[str, Any]],
    repository: str,
    now: datetime,
    pr_state: str = "open",
) -> int:
    """Chase a requested-but-undelivered retrospective; returns 1 if it acted.

    The third review-loop hook produces exactly one artifact — the verdict —
    and until now nothing asked whether it arrived.  A retrospective that was
    never written and one still being written are the same silence, which is
    how sokrates#1113's verdict sat on a disk for eight days with the loop
    reporting nothing wrong.

    Four facts gate the chase, and each one is a way of not inventing an
    obligation:

    * a **request receipt** for this head — a gate alone is not a request, and
      the scheduled exhaustion path posts a gate and wakes nobody;
    * **no delivery receipt** for this head;
    * the request is **dated** and older than ``RETROSPECTIVE_DELIVERY_SECONDS``
      — an undated receipt cannot be measured, and an unmeasurable window is
      reported, not assumed elapsed;
    * fewer than ``RETROSPECTIVE_CHASE_ATTEMPTS`` chases already spent.

    The first two are re-taken below on freshly fetched comments, past the head
    refresh and before the first act: ``comments`` is the scan's opening
    snapshot, the seat can deliver at any point inside that pass, and a chase
    decided on the snapshot accuses it of a silence it is not guilty of.

    Every one of them is keyed to the exact head, so a push after the gate
    ends the chase.  That is deliberate and it is the same rule the standing
    verdict follows: the moved head starts a fresh cycle, and asking for
    testimony about evidence the PR has left is asking for the wrong verdict.
    Which is why the head is re-decided at the publication too, and not only at
    the refresh: a snapshot head and a snapshot comment list go stale by the
    same push, and re-reading one of them was reading half the race (KRA-1374).

    It never gates, repairs, re-reviews, merges, or summons a reviewer
    (KRA-1029's charter); it asks only whether the verdict was delivered.
    """
    actor = retrospective_actor()
    if actor is None:
        # Held: no testimony is owed, so a receipt from before the hold is not
        # chased either — chasing would hound a seat the ruling excused.
        return 0
    if retrospective_delivered(comments, head_sha):
        return 0
    requested_at = retrospective_requested_at(comments, head_sha)
    if requested_at is None:
        # No receipt, or one with no usable timestamp.  Either way there is no
        # window to measure, and an unmeasured window is not an elapsed one.
        return 0
    if (now - requested_at).total_seconds() < RETROSPECTIVE_DELIVERY_SECONDS:
        return 0
    spent = retrospective_chase_attempts(comments, head_sha)
    if spent >= RETROSPECTIVE_CHASE_ATTEMPTS:
        return 0
    attempt = spent + 1
    # The second window runs from the last chase, not from the request: the
    # re-wake is what restarts the clock, so measuring both attempts off one
    # anchor would fire them on consecutive scans.
    if spent:
        last_chase_at = retrospective_chased_at(comments, head_sha, spent)
        if last_chase_at is None:
            print(
                f"undated retrospective chase marker on {repository}#{pr_number} "
                f"(head={head_sha}, attempt {spent}); not escalating"
            )
            return 0
        if (now - last_chase_at).total_seconds() < RETROSPECTIVE_DELIVERY_SECONDS:
            return 0
    if (
        refresh_pr_at_head(
            github,
            pr_number,
            head_sha,
            repository,
            action="retrospective chase",
            # The one publication whose subject survives closure: this leg is
            # deliberately swept over recently closed PRs, so the chokepoint's
            # liveness rule would delete it rather than protect it.  Head
            # exactness still refuses — a push after the gate ends the chase.
            require_open=False,
        )
        is None
    ):
        return 0

    def receipt_still_missing(comments: Sequence[Mapping[str, Any]]) -> bool:
        if retrospective_delivered(comments, head_sha):
            print(
                f"retrospective for {repository}#{pr_number} arrived while the chase "
                f"was being prepared (head={head_sha}); not chasing"
            )
            return False
        if retrospective_chase_attempts(comments, head_sha) >= attempt:
            print(
                f"retrospective chase attempt {attempt} for {repository}#{pr_number} "
                f"was already recorded (head={head_sha}); not chasing"
            )
            return False
        return True

    # ``comments`` was read at the top of the scan, and the seat this leg is
    # about to chase can post the retrospective at any moment inside that pass —
    # including while the head refresh above is in flight.  Acting on the stale
    # list costs a needless wake on attempt 1 and, on attempt 2, publicly states
    # that testimony was never delivered when it was.  The cheap re-read here
    # refuses that before the exemption file list and the publication-head GET;
    # those two requests reopen the same race, so the receipt is taken again
    # after them.  Pagination can span many HTTP requests, so a push during
    # that later call is a SHA the GET already accepted: the head is
    # re-decided after it, and the pair is what authorizes the acts.
    live = github.paginate(f"issues/{pr_number}/comments")
    if not receipt_still_missing(live):
        return 0
    # Last, and only here: a corpus declared exempt after the request leaves
    # every review-loop path, this chase included.  Asked after every cheap
    # gate so the closed sweep reads a file list only for a closure it is
    # actually about to chase, never for every closure in its window.
    if loop_exempt_pr(github, pr_number):
        print(
            f"loop-exempt PR {repository}#{pr_number} - retrospective chase "
            f"withdrawn (head={head_sha})"
        )
        return 0
    # The head is the other half of the same race as the comments above: a
    # push landing after the refresh ends the retrospective obligation by this
    # function's own contract, and the chase would then wake the seat for a
    # SHA the PR has left and, on the terminal attempt, state on the PR that
    # testimony is missing for evidence nobody owes testimony about.  Both
    # acts below take one head gate because they are one publication — the
    # marker records the wake, so a second head decision between them could
    # withhold the record of a wake already sent.
    if not publishable_at_head(
        github,
        pr_number,
        head_sha,
        repository,
        decision="retrospective chase",
        # The same waiver, for the same reason, as the refresh above: this
        # leg's subject survives closure, so only head exactness refuses here.
        require_open=False,
    ):
        return 0
    # The GET above sat between the last comments snapshot and the acts, so a
    # retrospective arriving while it is in flight would make an unchanged
    # head pass and the terminal attempt claim testimony was never delivered.
    # The receipt is taken after that call.  Pagination can span many HTTP
    # requests, widening the race past the single request
    # ``publishable_at_head`` documents, so a push during it is a SHA that GET
    # already accepted.  Re-deciding the head after the pagination binds the
    # pair: disagreement (a moved head) does not authorize.  A retrospective
    # that arrives during that last GET is the one-request residual the
    # chokepoint already names; another receipt read would reopen the push
    # window this closes.
    live = github.paginate(f"issues/{pr_number}/comments")
    if not receipt_still_missing(live):
        return 0
    if not publishable_at_head(
        github,
        pr_number,
        head_sha,
        repository,
        decision="retrospective chase",
        require_open=False,
    ):
        return 0
    if attempt < RETROSPECTIVE_CHASE_ATTEMPTS:
        # Slack first, then the marker: a marker written before a failed wake
        # would spend an attempt nobody received.
        slack = SlackApi(required_env("HIVE_BOT_TOKEN"), required_env("HIVE_CHANNEL"))
        slack.post_message(
            retrospective_chase_wake_message(
                pr_url=pr_url,
                pr_number=pr_number,
                repository=repository,
                head_sha=head_sha,
                requested_at=requested_at,
                pr_state=pr_state,
                actor=actor,
            )
        )
    github.post(
        f"issues/{pr_number}/comments",
        {"body": retrospective_chase_comment_body(head_sha, attempt, actor)},
    )
    print(
        f"chased undelivered retrospective for {repository}#{pr_number} "
        f"(head={head_sha}, attempt {attempt}/{RETROSPECTIVE_CHASE_ATTEMPTS})"
    )
    belt().event(
        "belt.retrospective.chase",
        **{
            "logfire.msg": (
                f"#{pr_number} retrospective undelivered: attempt {attempt}/"
                f"{RETROSPECTIVE_CHASE_ATTEMPTS}"
            ),
            "pull_request": pr_number,
            "head_sha": head_sha,
            "retrospective_actor": actor,
            "attempt": attempt,
            "max_attempts": RETROSPECTIVE_CHASE_ATTEMPTS,
            "pull_request_state": pr_state,
            "requested_at": requested_at.astimezone(timezone.utc).strftime(
                "%Y-%m-%dT%H:%M:%SZ"
            ),
            "undelivered_seconds": int((now - requested_at).total_seconds()),
        },
    )
    return 1


def chase_closed_pull_retrospectives(
    github: GitHubApi,
    *,
    repository: str,
    now: datetime,
) -> tuple[int, list[tuple[int, Exception]]]:
    """Chase pending retrospectives on recently closed PRs; ``(chased, errors)``.

    The other caller of the chase enumerates ``state="open"``, and a PR closed
    inside either delivery window would drop out of that enumeration with the
    request receipt still standing and nothing else ever reading it.  Closure
    there is a *normal* outcome, not an edge: the retrospective is testimony, it
    gates nothing, and the exhaustion gate hands the close to a human by design.
    The closure event itself cannot do this work either — at closure time the
    window has not elapsed, so a check there would always find nothing owed —
    which leaves a bounded backward sweep as the reconciliation that fits.

    The window is sized for the schedule, not for the work: both windows put the
    last possible chase within ~2h of the request, while the scheduled leg is
    throttled to a fire every ten hours or so under load and has to find the row
    when it next runs.  Re-sweeping is free of consequence — the delivery receipt
    and the attempt markers are the same durable state the open path reads, so a
    row with nothing outstanding returns 0 — and it costs one comment fetch per
    closed PR in the window.

    Errors are returned rather than raised: one unreadable closure must not
    abort the pass, or every eligible row behind it is re-skipped on every retry
    until it ages past the horizon.
    """
    horizon = now - timedelta(hours=RETROSPECTIVE_CLOSED_SWEEP_HOURS)
    chased = 0
    errors: list[tuple[int, Exception]] = []
    page = 1
    # Paged by hand, like the belt sweep: ``paginate`` materializes every page
    # before returning, and the horizon below can only bound a stream it reads.
    while True:
        batch = github.get(
            "pulls",
            query={
                "state": "closed",
                "sort": "updated",
                "direction": "desc",
                "per_page": 100,
                "page": page,
            },
        )
        if not isinstance(batch, list) or not batch:
            break
        stop = False
        for pull_request in batch:
            if not isinstance(pull_request, Mapping):
                continue
            # Closing a PR updates it, so ``updated_at >= closed_at``: once the
            # update stream falls past the horizon no later row can be inside it.
            if result_event_time(pull_request.get("updated_at")) < horizon:
                stop = True
                break
            if result_event_time(pull_request.get("closed_at")) < horizon:
                continue
            head = pull_request.get("head")
            if not isinstance(head, Mapping) or not head.get("sha"):
                continue
            number = int(pull_request.get("number") or 0)
            try:
                chased += chase_undelivered_retrospective(
                    github,
                    pr_number=number,
                    pr_url=str(
                        pull_request.get("html_url") or f"{repository}#{number}"
                    ),
                    head_sha=str(head["sha"]),
                    comments=github.paginate(f"issues/{number}/comments"),
                    repository=repository,
                    now=now,
                    pr_state=str(pull_request.get("state") or "closed"),
                )
            except Exception as error:  # noqa: BLE001 - one closure, not the pass.
                print(
                    f"closed-PR retrospective chase failed for "
                    f"{repository}#{number}: {type(error).__name__}: {error}",
                    file=sys.stderr,
                )
                errors.append((number, error))
                continue
        if stop or len(batch) < 100:
            break
        page += 1
    return chased, errors


def result_state_unchanged(
    snapshot: Mapping[str, Any] | None, live: Mapping[str, Any] | None
) -> bool:
    """Do two reads of one head's latest result describe the same event?

    Both sides are a ``latest_result_by_head`` entry, or ``None`` for a head
    that carries no result at all — which is precisely the state a nudge, a
    substitute summon and an exhaustion gate are computed from, so ``None`` on
    both sides is a match rather than an unknown.

    Every field must agree, and an event with no identity agrees with nothing,
    including another identity-less event: a record the loop cannot name cannot
    testify that the verdict state has not moved.  Comparing time alone is what
    made a same-second re-verdict invisible (KRA-1368); identity alone would
    miss an edited record, so both are checked, with the kind.
    """
    if snapshot is None or live is None:
        return snapshot is None and live is None
    identity = str(snapshot.get("identity") or "")
    if not identity or identity != str(live.get("identity") or ""):
        return False
    return snapshot.get("at") == live.get("at") and snapshot.get("kind") == live.get(
        "kind"
    )


def describe_result_state(state: Mapping[str, Any] | None) -> str:
    """One phrase naming a head's verdict state, for a refusal line."""
    if state is None:
        return "no verdict"
    at = state.get("at")
    stamp = (
        at.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        if isinstance(at, datetime)
        else "undated"
    )
    return f"{state.get('kind') or 'unknown'} at {stamp} ({state.get('identity') or 'unnamed'})"


def live_result_at_head(
    github: GitHubApi,
    *,
    pr_number: int,
    head_sha: str,
    codex_login: str,
) -> dict[str, Any] | None:
    """Re-read this head's latest result event straight from GitHub."""
    return latest_result_by_head(
        codex_result_events(
            github,
            github.paginate(f"pulls/{pr_number}/reviews"),
            github.paginate(f"issues/{pr_number}/comments"),
            codex_login,
            pr_number=pr_number,
        )
    ).get(head_sha)


def verdict_state_held(
    github: GitHubApi,
    *,
    pr_number: int,
    head_sha: str,
    codex_login: str,
    snapshot: Mapping[str, Any] | None,
    repository: str,
    action: str,
) -> bool:
    """Re-read the verdict at the publication itself; the one sweep-side gate.

    Every scheduled-leg publication — nudge, substitute summon, exhaustion
    gate, wake redelivery — is computed from reviews and comments snapshotted
    at the top of ``_scan_open_pull``.  Under the (event family, subject)
    concurrency key those runs share no group with ``verdict-<pr>``
    (KRA-1325), which is deliberate: serialising them would let one PR's
    comments evict another PR's verdict.  Revalidation, not serialisation, is
    the cure, and it belongs here rather than in each branch, because the
    branches disagreed about whether they needed it at all.

    ``refresh_pr_at_head`` / ``publishable_at_head`` re-check PR liveness and
    head equality only.  A head that stands still while a verdict lands on it
    passes both, so the snapshot was published anyway: a redundant ``@codex
    review`` or substitute summon spending a round on a head Codex had just
    answered, an exhaustion gate stopping automation on a head that had just
    gone CLEAN, or a stale digest re-delivered after the event route delivered
    the live one.

    Called immediately before the liveness chokepoint at each site, so the two
    reads that decide a publication are adjacent.
    """
    live = live_result_at_head(
        github, pr_number=pr_number, head_sha=head_sha, codex_login=codex_login
    )
    if result_state_unchanged(snapshot, live):
        return True
    print(
        f"refused {action} for {repository}#{pr_number} (head={head_sha}): the "
        f"live verdict is {describe_result_state(live)}, not the "
        f"{describe_result_state(snapshot)} this publication was computed from"
    )
    return False


def redeliver_standing_wake(
    github: GitHubApi,
    *,
    pull_request: Mapping[str, Any],
    pr_number: int,
    head_sha: str,
    reviews: Sequence[Mapping[str, Any]],
    comments: Sequence[Mapping[str, Any]],
    reviewed_heads: Sequence[str],
    repository: str,
    codex_login: str,
    now: datetime,
) -> bool:
    """Re-deliver one standing verdict for an already-reviewed head.

    Every review-loop wake fires exactly once, from an event-driven path.  A
    seat that consumed the wake without acting produces no further GitHub event,
    so the standing findings become invisible: the only clock-driven leg skips
    reviewed heads outright.  This is the backstop for that silence — attention
    only.  It adds no review round, no repair authority, and no merge authority,
    and it never summons a reviewer.

    "Acted" is a head change or any trusted head-disposition marker
    (``product-gate`` / ``noise`` / ``hold``) on this head dated at or after
    the standing verdict. An unchanged head past the window with none of those
    is a stall.
    """
    gate_state = exhaustion_marker_state(comments, head_sha)
    if gate_state == "terminal":
        # An exhaustion gate's terminal action is "stop and hold for the human".
        # That is observationally identical to consumed-without-action, and the
        # attention contract's "silence means stop safely" is load-bearing:
        # re-delivering it would convert a deliberate stop into pressure to act.
        return False
    if gate_state == "stale-policy":
        # The gate was written under a different round policy; the situation it
        # stopped no longer exists, so it must not stay terminal (KRA-1122).
        print(
            f"stale-policy exhaustion marker ignored for {repository}"
            f"#{pr_number} (head={head_sha}; policy now {MAX_REVIEW_ROUNDS})"
        )

    verdict_at = standing_verdict_time(github, reviews, comments, head_sha, codex_login)
    if verdict_at is None:
        print(
            f"no timestamped Codex verdict for {repository}#{pr_number} "
            f"(head={head_sha}); nothing to re-deliver"
        )
        return False
    # ``verdict_at <= disposed_at`` and not an unconditional stop, for the hold
    # as much as for the other two (KRA-1326 asked this to be decided): a
    # verdict that lands *after* the gate is news the gate's author has not
    # seen, it has already cost its round, and re-delivery is attention-only.
    # Silencing it would hide from the human exactly the review the incident
    # shows can still arrive at a held head.  Suppressing the *summon* is what
    # stops the round being spent; that is sited in ``_scan_open_pull``.
    for kind in HEAD_DISPOSITION_PREFIXES:
        disposed_at = head_disposed_at(kind, comments, head_sha)
        if disposed_at is not None and verdict_at <= disposed_at:
            print(
                f"{kind} recorded for {repository}#{pr_number} "
                f"(head={head_sha}); not a stall"
            )
            return False
    if (now - verdict_at).total_seconds() < WAKE_REDELIVERY_SECONDS:
        return False
    verdict_stamp = verdict_at.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    if redelivery_recorded(comments, head_sha, verdict_stamp):
        return False

    # The later same-head *kind* is authoritative: CLEAN clears the standing
    # digest.  A later findings review does not — GitHub does not resolve the
    # earlier review's comments, so the digest is the union since the most
    # recent CLEAN.  Zero retrievable inlines is not CLEAN.
    result_events = codex_result_events(
        github, reviews, comments, codex_login, pr_number=pr_number
    )
    snapshot_result = latest_result_by_head(result_events).get(head_sha)
    latest_kind = (snapshot_result or {}).get("kind")
    latest_review = latest_exact_head_review(reviews, head_sha, codex_login)
    clean_verdict = latest_kind == "clean"
    if clean_verdict:
        findings = []
    elif latest_kind == "findings":
        findings = standing_findings(
            github,
            pr_number,
            same_head_findings_reviews_since_clean(
                reviews, result_events, head_sha, codex_login
            ),
            codex_login,
        )
    else:
        print(
            f"no authoritative same-head verdict for {repository}#{pr_number} "
            f"(head={head_sha}); nothing to re-deliver"
        )
        return False
    substitute_standing = (
        standing_substitute_findings(comments, head_sha) if not clean_verdict else None
    )
    if not clean_verdict and not findings and substitute_standing is None:
        # A findings review whose inline comments are gone is not evidence of
        # CLEAN, and there is no digest to re-deliver.  A standing substitute
        # findings verdict IS a digest — its verdict comment — so it
        # re-delivers like any other standing findings state.
        return False
    if not clean_verdict and len(reviewed_heads) >= MAX_REVIEW_ROUNDS:
        # Defence behind the exhaustion marker above, for a head whose gate
        # comment failed to post: automation has stopped either way.
        return False

    resolved = author_for_pr(github, pr_number, head_sha, pull_request)
    if resolved is None:
        return False
    author, author_actor = resolved

    pr_state = refresh_pr_at_head(
        github, pr_number, head_sha, repository, action="wake redelivery"
    )
    if pr_state is None:
        return False
    refreshed_head = pr_state.get("head")
    if not isinstance(refreshed_head, Mapping):
        raise TypeError("live pull_request.head is missing")
    if not clean_verdict and not findings and substitute_standing is None:
        return False
    branch = str(refreshed_head["ref"])
    pr_url = str(pr_state.get("html_url") or f"{repository}#{pr_number}")
    review_round = result_round_for_head(reviewed_heads, head_sha)

    if clean_verdict:
        live_base_ref, _live_base_sha = pr_base(pr_state)
        stale_ref = stale_base_ref_for_closure(comments, head_sha, live_base_ref)
        if stale_ref is not None:
            print(
                f"refused clean redelivery for {repository}#{pr_number}: head "
                f"{head_sha} was reviewed against base ref `{stale_ref}` but "
                f"the PR now targets `{live_base_ref}` — the standing verdict "
                "no longer names the reviewed subject"
            )
            return False
        retargeted_at = base_retarget_after(github, pr_number, verdict_stamp)
        if retargeted_at is not None:
            print(
                f"refused clean redelivery for {repository}#{pr_number}: the "
                f"PR base was retargeted at `{retargeted_at}`, after the "
                "standing verdict was formed — it no longer names the "
                "reviewed subject"
            )
            return False
        messages = [
            clean_wake_message(
                author_actor=author_actor,
                author=author,
                head_sha=head_sha,
                review_round=review_round,
                review_state="clean-comment",
                pr_url=pr_url,
                branch=branch,
            )
        ]
    else:
        base_ref, base_sha = pr_base(pr_state)
        review_comments = github.paginate(f"pulls/{pr_number}/comments")
        history = round_history(
            reviewed_heads,
            reviews,
            review_comments,
            codex_login,
            latest_results=latest_result_by_head(result_events),
            issue_comments=comments,
        )
        # Mixed sources on one head (Codex inline findings AND a later
        # substitute verdict): the latest source is the primary verdict, and
        # the other source's digest still rides in the same wake — the burn
        # seat must never act on a partial evidence set.
        substitute_is_latest = substitute_standing is not None and (
            latest_review is None
            or substitute_standing[1]["at"]
            >= result_event_time(latest_review.get("submitted_at"))
        )
        if findings and not substitute_is_latest:
            assert latest_review is not None
            review_state = str(latest_review.get("state") or "unknown")
            substitute_payload = None
        else:
            assert substitute_standing is not None
            substitute_comment, substitute_verdict_parsed = substitute_standing
            review_state = f"substitute-findings:{substitute_verdict_parsed['actor']}"
            substitute_payload = {
                "actor": substitute_verdict_parsed["actor"],
                "counts": substitute_verdict_parsed["counts"],
                "body": str(substitute_comment.get("body") or ""),
            }
        messages = build_burn_messages(
            findings=findings,
            review_state=review_state,
            substitute=substitute_payload,
            cast=burn_cast(),
            effort=burn_effort(pr_labels(pull_request)),
            pr_url=pr_url,
            branch=branch,
            head_sha=head_sha,
            base_ref=base_ref,
            base_sha=base_sha,
            repository=repository,
            author=author,
            author_actor=author_actor,
            review_round=review_round,
            history=history,
        )
    messages[0] = f"{redelivery_notice(verdict_stamp)}\n\n{messages[0]}"

    slack = SlackApi(required_env("HIVE_BOT_TOKEN"), required_env("HIVE_CHANNEL"))
    # This leg publishes directly rather than through ``deliver_wake`` (its
    # record is ``belt.redelivery``, not ``belt.delivery``), so the publication
    # boundary is re-checked here for the same reason: the reads above —
    # author, retarget probe, review comments, history — all happen after the
    # route's own refresh, and a PR that merged inside that window must not be
    # re-delivered to a seat.
    #
    # Liveness is not enough.  The reviews and comments this wake was built
    # from were snapshotted at the top of the scan; ``verdict-<pr>`` can
    # publish a newer same-head verdict while that scan is still in
    # ``sweep``.  Re-validate the standing verdict immediately before the
    # liveness check, or a stale CLEAN follows a live findings wake and
    # invites a merge.
    if not verdict_state_held(
        github,
        pr_number=pr_number,
        head_sha=head_sha,
        codex_login=codex_login,
        snapshot=snapshot_result,
        repository=repository,
        action="wake redelivery",
    ):
        return False
    if not publishable_at_head(
        github, pr_number, head_sha, repository, decision="redelivery"
    ):
        return False
    try:
        post_threaded_messages(
            slack,
            messages,
            github=github,
            repository=repository,
            pr_number=pr_number,
            head_sha=head_sha,
            decision="redelivery",
        )
    except PublicationWithheld:
        # The check above protects the thread root; the protocol's own check
        # protects the dispatch, and a refusal there is this leg's refusal one
        # HTTP hop later.  No marker: the one redelivery this verdict gets was
        # never delivered, and duplicate delivery is the safe direction.
        return False
    # Slack first, then the marker. A Slack failure leaves no marker, so the next
    # tick retries — duplicate delivery is the safe direction. A marker failure
    # after a successful post raises out of the scan rather than being swallowed.
    github.post(
        f"issues/{pr_number}/comments",
        {"body": redelivery_comment_body(head_sha, verdict_stamp)},
    )
    print(
        f"re-delivered standing wake for {repository}#{pr_number} "
        f"(head={head_sha}, findings={len(findings)}, verdict={verdict_stamp})"
    )
    belt().event(
        "belt.redelivery",
        **{
            "logfire.msg": f"#{pr_number} standing verdict re-delivered",
            "pull_request": pr_number,
            "head_sha": head_sha,
            "findings_total": len(findings),
            "verdict_kind": "clean" if clean_verdict else "findings",
            "verdict_at": verdict_stamp,
            "wake_chunks": len(messages),
            "rounds_consumed": len(reviewed_heads),
        },
    )
    return True


def usage_snapshot() -> Mapping[str, Any] | None:
    """One ``GET /v3/usage`` against the AI-usage aggregator; ``None`` means absent.

    The fetch primitive under every meter read (the Codex find-half meter and
    the burn cast).  Advisory: unset env, network, non-2xx and an unparseable
    body all collapse to ``None`` and the caller behaves as if no meter
    existed.  The bearer token is used and never returned, logged or
    embedded in output.
    """
    base_url = os.environ.get("AI_USAGE_URL", "").strip().rstrip("/")
    token = os.environ.get("AI_USAGE_READ_TOKEN", "").strip()
    if not base_url or not token:
        return None
    request = urllib.request.Request(
        f"{base_url}/v3/usage",
        headers={
            "Accept": "application/json",
            "Authorization": f"Bearer {token}",
            "User-Agent": "weave-doctrine-review-loop",
        },
        method="GET",
    )
    try:
        with urllib.request.urlopen(request, timeout=5) as response:
            payload = json.loads(response.read().decode("utf-8"))
    except Exception:  # noqa: BLE001 - advisory meter: every failure is "absent".
        return None
    return payload if isinstance(payload, Mapping) else None


def usage_meter_reading() -> dict[str, Any] | None:
    """Read the Codex pool from the AI-usage aggregator; ``None`` means absent.

    The meter is advisory routing input, never a gate: ANY failure — unset
    env, network, non-2xx, unparseable body, unknown pool — collapses to
    ``None`` and the caller behaves exactly as it did before the meter
    existed.  A dead meter must not add a way for the belt to hang.  The
    bearer token is used and never returned, logged, or embedded in output.
    """
    pool_name = os.environ.get("AI_USAGE_CODEX_POOL", "").strip()
    payload = usage_snapshot()
    if payload is None:
        return None
    pools = payload.get("pools")
    if not isinstance(pools, Sequence):
        return None
    # Schema-3 pool selection: the pool `id` is an opaque identity digest, so
    # the default match is `provider == "codex"`; AI_USAGE_CODEX_POOL, when
    # set, narrows by exact `id` or human `label`.  With several connected
    # codex pools and no narrowing, payload order is not an identity — the
    # most-constrained window across EVERY matching pool governs routing
    # (route away if any connected pool is hot), never first-in-array.
    utilization: float | None = None
    resets_at: Any = None
    for candidate in pools:
        if not isinstance(candidate, Mapping):
            continue
        if candidate.get("provider") != "codex":
            continue
        if pool_name and pool_name not in (candidate.get("id"), candidate.get("label")):
            continue
        windows = candidate.get("windows")
        if not isinstance(windows, Sequence):
            continue
        for window in windows:
            if not isinstance(window, Mapping):
                continue
            value = window.get("utilization")
            if not isinstance(value, (int, float)) or not 0 <= float(value) <= 1:
                continue
            if utilization is None or float(value) > utilization:
                utilization = float(value)
                resets_at = window.get("resets_at")
    if utilization is None:
        return None
    return {
        "utilization": utilization,
        "resets_at": str(resets_at) if resets_at else None,
    }


def codex_threshold() -> float:
    raw = os.environ.get("AI_USAGE_CODEX_THRESHOLD", "").strip()
    try:
        value = float(raw)
    except ValueError:
        return AI_USAGE_DEFAULT_THRESHOLD
    if not 0 < value <= 1:
        return AI_USAGE_DEFAULT_THRESHOLD
    return value


# --- seat-router (vendored) ------------------------------------------------
# One fold, two callers: the review loop casts its burn seat with it and the
# Linear dispatcher casts a ticket's default seat with it.  Both scripts are
# single-file deployables, so the block is vendored verbatim into each;
# tests/test_seat_router_vendored.py fails the moment the two copies differ.
#
# The input is the AI-usage aggregator's schema-3 ``/v3/usage`` snapshot.  A
# seat is joined to a pool through the pool's observed profiles: the profile
# id the collector publishes is ``<seat>-<edge>`` (``gnomon-cx53``,
# ``talos-cx43``, ``fable-laptop``), so the join is ``id == seat`` or
# ``id.startswith(seat + "-")``; a seat whose collector names its profile
# differently is declared once as ``seat=profile-id`` in the override map.
# A seat no profile matches is *unknown*, never available and never
# excluded — unobserved is not the same evidence as exhausted (Talos, 2026-09-07:
# a burn seat that was dry for a day while the belt kept minting to it).
SEAT_AVAILABILITY_THRESHOLD_DEFAULT = 0.9
_SEAT_PROFILE_STATE_RANK = {"current": 0, "recent": 1, "stale": 2}


def seat_usage_profiles(raw: str) -> dict[str, str]:
    """``seat=profile-id,seat2=profile-id2`` → ``{seat: profile-id}``.

    Malformed entries (no ``=``, empty side) are dropped; the map is advisory
    routing input and a typo must not raise inside a wake leg.
    """
    profiles: dict[str, str] = {}
    for entry in raw.split(","):
        seat, separator, profile_id = entry.strip().partition("=")
        seat = seat.strip().lower()
        profile_id = profile_id.strip()
        if separator and seat and profile_id:
            profiles[seat] = profile_id
    return profiles


def _seat_matches_profile(
    seat: str, profile: Mapping[str, Any], override: str | None
) -> bool:
    profile_id = str(profile.get("id") or "")
    if override is not None:
        return profile_id == override
    label = str(profile.get("label") or "").strip().lower()
    return profile_id == seat or profile_id.startswith(f"{seat}-") or label == seat


def _pool_peak_window(pool: Mapping[str, Any]) -> tuple[float | None, str | None]:
    """The most constrained window of a pool: ``(utilization, resets_at)``."""
    utilization: float | None = None
    resets_at: str | None = None
    windows = pool.get("windows")
    if not isinstance(windows, Sequence):
        return None, None
    for window in windows:
        if not isinstance(window, Mapping):
            continue
        value = window.get("utilization")
        if not isinstance(value, (int, float)) or not 0 <= float(value) <= 1:
            continue
        if utilization is None or float(value) > utilization:
            utilization = float(value)
            resets = window.get("resets_at")
            resets_at = str(resets) if resets else None
    return utilization, resets_at


def seat_availability(
    snapshot: Mapping[str, Any] | None,
    roster: Sequence[str],
    *,
    threshold: float = SEAT_AVAILABILITY_THRESHOLD_DEFAULT,
    profiles: Mapping[str, str] | None = None,
) -> dict[str, dict[str, Any]]:
    """Per roster seat: ``state`` ∈ available|exhausted|unavailable|unknown.

    ``available``: the joined pool reports ``status == "ok"``, its observing
    profile is not ``stale``, and the peak window sits under ``threshold``.
    ``exhausted``: the peak window is at or over ``threshold`` (``resets_at``
    says when it clears).  ``unavailable``: the pool's status is anything but
    ``ok`` (``auth_expired``, ``billing_unavailable``, ``error``, ``stale``) or
    the profile is stale.  ``unknown``: no profile in the snapshot joins the
    seat.  ``detail`` is a one-clause human reading for the wake (R-3).
    """
    override = dict(profiles or {})
    states: dict[str, dict[str, Any]] = {
        seat: {
            "state": "unknown",
            "utilization": None,
            "resets_at": None,
            "detail": "usage unobserved",
        }
        for seat in roster
    }
    pools = snapshot.get("pools") if isinstance(snapshot, Mapping) else None
    if not isinstance(pools, Sequence):
        return states
    best_rank: dict[str, int] = {}
    for pool in pools:
        if not isinstance(pool, Mapping):
            continue
        pool_profiles = pool.get("profiles")
        if not isinstance(pool_profiles, Sequence):
            continue
        status = str(pool.get("status") or "unknown")
        utilization, resets_at = _pool_peak_window(pool)
        for profile in pool_profiles:
            if not isinstance(profile, Mapping):
                continue
            profile_state = str(profile.get("state") or "current")
            rank = _SEAT_PROFILE_STATE_RANK.get(profile_state, 3)
            for seat in roster:
                if not _seat_matches_profile(seat, profile, override.get(seat)):
                    continue
                if seat in best_rank and best_rank[seat] <= rank:
                    continue
                best_rank[seat] = rank
                if status != "ok":
                    reading = {"state": "unavailable", "detail": status}
                elif profile_state == "stale":
                    reading = {"state": "unavailable", "detail": "profile stale"}
                elif utilization is None:
                    reading = {"state": "unknown", "detail": "no usage window"}
                elif utilization >= threshold:
                    reading = {
                        "state": "exhausted",
                        "detail": f"exhausted {utilization:.2f}"
                        + (f" (resets {resets_at})" if resets_at else ""),
                    }
                else:
                    reading = {"state": "available", "detail": f"ok {utilization:.2f}"}
                states[seat] = {
                    **reading,
                    "utilization": utilization,
                    "resets_at": resets_at,
                }
    return states


def cast_seat(
    roster: Sequence[str],
    snapshot: Mapping[str, Any] | None,
    *,
    cast: str,
    threshold: float = SEAT_AVAILABILITY_THRESHOLD_DEFAULT,
    profiles: Mapping[str, str] | None = None,
) -> tuple[str, str]:
    """``(actor, note)``: the first roster seat the meter reads as available.

    A roster of at most one seat, or an absent snapshot, is the pre-meter
    behaviour: the cast seat, no note.  Otherwise roster order is preference:
    the first ``available`` seat wins; with none, the first ``unknown`` seat
    (unobserved beats exhausted); with none of those either, the cast seat —
    named as a fallback, so a wake to a seat the meter could not clear is
    visibly the meter's failure, not its choice.  The note is the R-3
    publication of the reading and ends in a newline; an empty note means the
    meter did not speak.
    """
    ordered = [
        seat for seat in dict.fromkeys(seat.strip().lower() for seat in roster) if seat
    ]
    if len(ordered) <= 1 or snapshot is None:
        return cast, ""
    states = seat_availability(
        snapshot, ordered, threshold=threshold, profiles=profiles
    )
    reading = " · ".join(f"{seat} {states[seat]['detail']}" for seat in ordered)
    for seat in ordered:
        if states[seat]["state"] == "available":
            return seat, f"Cast by the meter: {reading} → {seat}.\n"
    for seat in ordered:
        if states[seat]["state"] == "unknown":
            return (
                seat,
                f"Cast by the meter: {reading} → {seat} (unobserved; no seat reads available).\n",
            )
    return cast, (
        f"Cast by the meter: {reading} → every roster seat is exhausted or "
        f"unavailable; falling back to the cast seat {cast}.\n"
    )


# --- end seat-router (vendored) --------------------------------------------


def normalize_substitute_actor(raw: str) -> str | None:
    """Map a configured actor onto the verdict-marker grammar, or ``None``.

    The marker contract is ``SUBSTITUTE_ACTOR_TOKEN``. Case and underscores
    are recoverable; anything else cannot become a parseable marker without
    inventing identity, so it is refused.
    """
    normalized = raw.strip().lower().replace("_", "-")
    if not SUBSTITUTE_ACTOR_RE.fullmatch(normalized):
        return None
    return normalized


def substitute_actor() -> str:
    raw = (
        os.environ.get("REVIEW_SUBSTITUTE_ACTOR", "").strip()
        or DEFAULT_SUBSTITUTE_ACTOR
    )
    actor = normalize_substitute_actor(raw)
    if actor is None:
        raise ValueError(
            f"REVIEW_SUBSTITUTE_ACTOR={raw!r} is outside the substitute "
            "verdict grammar [a-z0-9-]+ after normalization; refusing to "
            "summon an unparseable reviewer"
        )
    return actor


def burn_actor() -> str:
    """The seat every burn wake addresses; same normalization as the reviewer.

    The token doubles as the WAKE envelope's actor, so the marker grammar is
    also the envelope grammar — an unroutable name is refused here, not
    discovered as a dead-lettered wake.
    """
    raw = os.environ.get("REVIEW_BURN_ACTOR", "").strip() or DEFAULT_BURN_ACTOR
    actor = normalize_substitute_actor(raw)
    if actor is None:
        raise ValueError(
            f"REVIEW_BURN_ACTOR={raw!r} is outside the actor grammar "
            "[a-z0-9-]+ after normalization; refusing to wake an "
            "unroutable burn seat"
        )
    return actor


def retrospective_actor() -> str | None:
    """The seat the exhaustion gate wakes, or ``None`` while the hook is held.

    Unset names the charter seat (``RETROSPECTIVE_ACTOR``).  A hold value
    posts the human gate and wakes nobody — Hákon's ruling of 2026-09-07 for
    the thirteen-lanes crunch.  Anything else is a seat name under the same
    grammar the other two casts use, refused here rather than dead-lettered.
    """
    raw = os.environ.get(RETROSPECTIVE_ACTOR_ENV, "").strip()
    if not raw:
        return RETROSPECTIVE_ACTOR
    if raw.lower() in RETROSPECTIVE_HOLD_VALUES:
        return None
    actor = normalize_substitute_actor(raw)
    if actor is None:
        raise ValueError(
            f"{RETROSPECTIVE_ACTOR_ENV}={raw!r} is outside the actor grammar "
            "[a-z0-9-]+ after normalization and is not a hold value "
            f"({'|'.join(sorted(RETROSPECTIVE_HOLD_VALUES))}); refusing to "
            "wake an unroutable retrospective seat"
        )
    return actor


def burn_roster() -> tuple[str, ...]:
    """``REVIEW_BURN_ROSTER`` in preference order; empty when unset.

    Each name goes through the actor grammar; an unroutable name is refused
    for the same reason ``burn_actor`` refuses one.
    """
    seats: list[str] = []
    for part in os.environ.get(BURN_ROSTER_ENV, "").split(","):
        if not part.strip():
            continue
        actor = normalize_substitute_actor(part)
        if actor is None:
            raise ValueError(
                f"{BURN_ROSTER_ENV} entry {part!r} is outside the actor grammar "
                "[a-z0-9-]+ after normalization; refusing an unroutable roster"
            )
        if actor not in seats:
            seats.append(actor)
    return tuple(seats)


def burn_threshold() -> float:
    raw = os.environ.get(BURN_THRESHOLD_ENV, "").strip()
    try:
        value = float(raw)
    except ValueError:
        return SEAT_AVAILABILITY_THRESHOLD_DEFAULT
    if not 0 < value <= 1:
        return SEAT_AVAILABILITY_THRESHOLD_DEFAULT
    return value


def burn_cast() -> tuple[str, str]:
    """``(actor, note)`` for the next burn wake: the roster read by the meter.

    No roster, or no meter, is the static cast with an empty note — the
    wake is byte-identical to the pre-roster belt.
    """
    cast = burn_actor()
    roster = burn_roster()
    if len(roster) <= 1:
        return cast, ""
    return cast_seat(
        roster,
        usage_snapshot(),
        cast=cast,
        threshold=burn_threshold(),
        profiles=seat_usage_profiles(os.environ.get(SEAT_USAGE_PROFILES_ENV, "")),
    )


def pr_labels(pull_request: Mapping[str, Any] | None) -> list[str]:
    """Label names on a PR object; tolerant of the list shape and of ``None``."""
    if not isinstance(pull_request, Mapping):
        return []
    labels = pull_request.get("labels")
    if not isinstance(labels, Sequence):
        return []
    return [
        str(label.get("name") or "")
        for label in labels
        if isinstance(label, Mapping) and label.get("name")
    ]


def burn_effort(labels: Sequence[str]) -> str | None:
    """The ``Effort:`` tier a burn wake carries, or ``None`` for no overlay.

    Exactly one valid ``effort:<tier>`` PR label wins; two distinct tiers are
    a human ambiguity and yield no overlay (named on stdout, never guessed).
    With no label, ``REVIEW_BURN_EFFORT`` applies when it names a tier.
    """
    requested = sorted(
        {
            name[len(EFFORT_LABEL_PREFIX) :].strip().lower()
            for name in labels
            if name.lower().startswith(EFFORT_LABEL_PREFIX)
        }
    )
    valid = [tier for tier in requested if tier in WAKE_EFFORT_TIERS]
    if len(valid) > 1:
        print(f"effort labels ambiguous ({', '.join(valid)}); no overlay applied")
        return None
    if len(valid) == 1:
        return valid[0]
    raw = os.environ.get(BURN_EFFORT_ENV, "").strip().lower()
    if not raw:
        return None
    if raw not in WAKE_EFFORT_TIERS:
        print(
            f"{BURN_EFFORT_ENV}={raw!r} is not a tier ({'|'.join(WAKE_EFFORT_TIERS)}); ignored"
        )
        return None
    return raw


def quota_refusal_is_latest_codex_signal(
    reviews: Sequence[Mapping[str, Any]],
    comments: Sequence[Mapping[str, Any]],
    codex_login: str,
) -> bool:
    """True when the newest thing Codex said on this PR is a quota refusal.

    Evidence-ordered, not clock-windowed: a refusal is live until Codex itself
    supersedes it with any later signal (a review, a clean comment, a verdict,
    even another error shape).  That needs no reset-period knob and cannot go
    stale silently — the moment Codex speaks again, the refusal stops routing.
    """
    latest_refusal: datetime | None = None
    latest_other: datetime | None = None
    for review in reviews:
        user = review.get("user")
        if not isinstance(user, Mapping) or user.get("login") != codex_login:
            continue
        at = result_event_time(review.get("submitted_at"))
        # A usage-limit refusal can arrive as a submitted review, not only a
        # comment (the connector auto-fires on push); classifying it as a
        # superseding "other" signal would flip the route straight back into
        # another refusal.
        body = str(review.get("body") or "")
        if is_quota_refusal_body(body):
            if latest_refusal is None or at > latest_refusal:
                latest_refusal = at
        elif latest_other is None or at > latest_other:
            latest_other = at
    for comment in comments:
        user = comment.get("user")
        if not isinstance(user, Mapping) or user.get("login") != codex_login:
            continue
        at = result_event_time(comment.get("created_at"))
        body = str(comment.get("body") or "")
        if is_quota_refusal_body(body):
            if latest_refusal is None or at > latest_refusal:
                latest_refusal = at
        elif latest_other is None or at > latest_other:
            latest_other = at
    if latest_refusal is None:
        return False
    # GitHub stamps these events to whole seconds, so a refusal and another
    # signal can tie. A tie keeps the refusal live: routing the substitute
    # once more is attention-only, routing back to Codex elicits another
    # refusal and loses the evidence.
    return latest_other is None or latest_refusal >= latest_other


def find_half_route(
    reviews: Sequence[Mapping[str, Any]],
    comments: Sequence[Mapping[str, Any]],
    codex_login: str,
    *,
    usage_meter: Mapping[str, Any] | None | object = _FETCH_METER,
) -> tuple[str, str]:
    """Choose the find half for one summon: ``("codex" | "substitute", reason)``.

    A pure selection fold in front of the existing summon code — it never
    posts, never raises, and its reason string is published with the summon so
    the thread shows why a reviewer was chosen (R-3).  Fail-open by
    construction: with no meter and no observed refusal the answer is Codex,
    byte-identical to the pre-router loop.

    ``usage_meter`` is the scan's one account-wide reading when supplied;
    omitted, this fold fetches.  The scheduled scan must pass the reading so
    a black-holing aggregator cannot charge one timeout per stalled PR.
    """
    if quota_refusal_is_latest_codex_signal(reviews, comments, codex_login):
        return (
            "substitute",
            (
                "Codex's latest signal on this PR is a usage-limits refusal "
                "(unsuperseded), so a nudge would burn another refusal"
            ),
        )
    meter = usage_meter_reading() if usage_meter is _FETCH_METER else usage_meter
    if meter is None:
        return ("codex", "usage meter absent; default find half")
    threshold = codex_threshold()
    resets = meter["resets_at"] or "unknown"
    if meter["utilization"] >= threshold:
        return (
            "substitute",
            (
                f"Codex pool utilization {meter['utilization']:.2f} >= "
                f"threshold {threshold:.2f} (resets_at {resets})"
            ),
        )
    return (
        "codex",
        (
            f"Codex pool utilization {meter['utilization']:.2f} < "
            f"threshold {threshold:.2f} (resets_at {resets})"
        ),
    )


def substitute_summon_marker(head_sha: str) -> str:
    return f"{SUBSTITUTE_SUMMON_MARKER_PREFIX}{head_sha} -->"


def substitute_summon_covers_head(
    comments: Sequence[Mapping[str, Any]], head_sha: str
) -> bool:
    return marker_comment_exists(comments, substitute_summon_marker(head_sha))


def substitute_verdict_clean_marker(head_sha: str, actor: str) -> str:
    """The exact-head CLEAN verdict a substitute reviewer types."""
    return f"{SUBSTITUTE_VERDICT_MARKER_PREFIX}{head_sha}:{actor}:clean -->"


def substitute_verdict_findings_marker(
    head_sha: str, actor: str, p1: int | str, p2: int | str, p3: int | str
) -> str:
    """The exact-head findings verdict a substitute reviewer types, counts by severity."""
    return (
        f"{SUBSTITUTE_VERDICT_MARKER_PREFIX}{head_sha}:{actor}"
        f":findings:{p1}:{p2}:{p3} -->"
    )


def substitute_verdict_marker_line(head_sha: str, actor: str) -> str:
    """The marker contract quoted verbatim in the summon, so the substitute
    can copy it rather than reconstruct it."""
    return (
        f"CLEAN: `{substitute_verdict_clean_marker(head_sha, actor)}`\n"
        f"Findings: `{substitute_verdict_findings_marker(head_sha, actor, '<p1>', '<p2>', '<p3>')}` "
        "(counts by severity), plus the findings themselves in the same comment."
    )


def substitute_summon_comment_body(
    *, head_sha: str, actor: str, reason: str, review_round: int
) -> str:
    """PR-side record of a substitute summon: dedupe marker + routing decision.

    This is the audit trail the nudge marker provides for Codex summons — a
    scan that finds it does not summon this head again, and a reader of the PR
    sees why Codex was not asked.
    """
    return (
        f"Review-loop router: summoned substitute reviewer `{actor}` for head "
        f"`{head_sha}` (round {review_round}/{MAX_REVIEW_ROUNDS}).\n"
        f"Route reason: {reason}.\n"
        f"{substitute_summon_marker(head_sha)}"
    )


def substitute_review_wake_message(
    *,
    actor: str,
    reason: str,
    pr_url: str,
    branch: str,
    head_sha: str,
    review_round: int,
    repository: str,
) -> str:
    return (
        f"WAKE: {actor}\n\n"
        "Review-loop router: the Codex find half is unavailable for this "
        f"summon ({reason}). You hold this review round — load skill "
        "`code-review` and its Weave integration reference; "
        "they define this seat's review and delivery contract.\n\n"
        f"{SCOPE_TEST_REVIEWER}\n\n"
        f"PR: {pr_url}\n"
        f"Repo: `{repository}`\n"
        f"Branch: `{branch}`\n"
        f"Head: `{head_sha}` (round {review_round}/{MAX_REVIEW_ROUNDS})\n\n"
        "Post your exact-head verdict as a PR conversation comment that "
        "includes the matching marker line verbatim — the marker, not the "
        "prose, is what the loop reads:\n"
        f"{substitute_verdict_marker_line(head_sha, actor)}\n\n"
        "Do not nudge @codex (a summons while it is unavailable burns a "
        "refusal). Do not merge: closure and merge stay with the loop's "
        "composed boundary."
    )


class ScanCompletedWithErrors(RuntimeError):
    """The scheduled scan finished, but one or more PRs failed reconciliation.

    Raised *after* the loop so the workflow run still terminalizes red (R-3)
    without one poisoned PR blinding every PR enumerated after it.

    Every scheduled scan over a window of PRs owes this shape.  A scan that
    lets one row abort the pass re-skips the same survivors on every retry
    for as long as the poisoned row stays in the window, which is silence
    that looks exactly like an empty window.
    """

    def __init__(self, scan: str, errors: Sequence[tuple[int, Exception]]) -> None:
        self.scan = scan
        self.errors = list(errors)
        summary = "; ".join(
            f"#{number}: {type(error).__name__}: {error}"
            for number, error in self.errors
        )
        super().__init__(
            f"{scan} scan completed with {len(self.errors)} PR error(s): {summary}"
        )


def _scan_open_pull(
    github: GitHubApi,
    pull_request: Mapping[str, Any],
    *,
    repository: str,
    codex_login: str,
    now: datetime,
    usage_meter: Mapping[str, Any] | None | object = _FETCH_METER,
    stall_gate: bool = True,
) -> tuple[int, int, int, int]:
    """Reconcile one open PR; returns ``(nudged, summoned, redelivered, chased)``.

    ``stall_gate=False`` is the event path: a live quota refusal has already
    proven the head will not be reviewed by waiting, so the commit-age
    threshold that keeps the scheduled scan patient does not apply.
    """
    head = pull_request.get("head")
    if not isinstance(head, Mapping):
        return (0, 0, 0, 0)
    commit = github.get(f"commits/{head['sha']}")
    author = commit_author_name(commit)
    if author not in seat_map(same_repo=head_is_same_repo(pull_request)):
        return (0, 0, 0, 0)
    committed_at = review_stall_anchor(commit, pull_request, now)
    if stall_gate and (now - committed_at).total_seconds() < REVIEW_STALL_SECONDS:
        return (0, 0, 0, 0)
    pr_number = int(pull_request["number"])
    if loop_exempt_pr(github, pr_number):
        # No summon, no nudge, no redelivery, no exhaustion gate: the corpus's
        # own gate (weekly skill audit, or the repo's mechanical CI for its
        # declared recipe and law roots) is the whole quality bar.
        print(f"loop-exempt PR {repository}#{pr_number} - review loop exempt")
        return (0, 0, 0, 0)
    reviews = github.paginate(f"pulls/{pr_number}/reviews")
    head_sha = str(head["sha"])
    comments = github.paginate(f"issues/{pr_number}/comments")
    # Before every branch below, because an exhausted head returns early on
    # both of the first two: a delivery check sited after either one would
    # never run on the exact PRs it exists for.  It is independent of the
    # routing decisions that follow — it summons nobody and changes no round
    # count — so it neither consumes nor is consumed by them.
    chased = chase_undelivered_retrospective(
        github,
        pr_number=pr_number,
        pr_url=str(pull_request.get("html_url") or f"{repository}#{pr_number}"),
        head_sha=head_sha,
        comments=comments,
        repository=repository,
        now=now,
    )
    result_events = codex_result_events(
        github, reviews, comments, codex_login, pr_number=pr_number
    )
    reviewed_heads = result_heads_from_events(result_events)
    # The verdict state every branch below publishes from, read off the same
    # event stream that decides which branch runs.  Today it is always None on
    # the three publishing branches — they are reached only past the
    # ``head_sha in reviewed_heads`` return — so this derivation and a literal
    # ``None`` are behaviourally identical.  It is derived anyway: a change to
    # that branch condition would otherwise leave three publications silently
    # asserting a premise nothing re-establishes, and the equivalence the
    # literal would depend on is a property of two other functions
    # (``result_heads_from_events`` and ``latest_result_by_head`` key one
    # stream the same way), not of this one.  Each publication then re-reads
    # the state live at the post itself (KRA-1368).
    snapshot_result = latest_result_by_head(result_events).get(head_sha)
    if head_sha in reviewed_heads:
        # A reviewed head needs no reviewer, but its verdict may still be
        # standing unacted. The commit-age gate above is already satisfied
        # here: a verdict old enough to re-deliver sits on a commit that is
        # older still, and the future-commit fallback clears twenty minutes
        # of PR quiet on its own.
        if redeliver_standing_wake(
            github,
            pull_request=pull_request,
            pr_number=pr_number,
            head_sha=head_sha,
            reviews=reviews,
            comments=comments,
            reviewed_heads=reviewed_heads,
            repository=repository,
            codex_login=codex_login,
            now=now,
        ):
            return (0, 0, 1, chased)
        return (0, 0, 0, chased)
    if len(reviewed_heads) >= MAX_REVIEW_ROUNDS:
        pr_url = str(pull_request.get("html_url") or f"{repository}#{pr_number}")
        gate = exhaustion_gate(
            pr_url=pr_url,
            head_sha=head_sha,
            reviewed_heads=len(reviewed_heads),
            reason=(
                "The current head has no exact-head Codex review after the "
                "bounded automatic review cycle."
            ),
        )
        gate_state = exhaustion_marker_state(comments, head_sha)
        if gate_state != "terminal":
            if gate_state == "stale-policy":
                print(
                    f"re-posting exhaustion gate for {repository}"
                    f"#{pr_number} (head={head_sha}): the prior gate "
                    "recorded a different policy"
                )
            if not verdict_state_held(
                github,
                pr_number=pr_number,
                head_sha=head_sha,
                codex_login=codex_login,
                snapshot=snapshot_result,
                repository=repository,
                action="exhaustion gate",
            ):
                return (0, 0, 0, chased)
            pr_state = refresh_pr_at_head(
                github,
                pr_number,
                head_sha,
                repository,
                action="exhaustion gate",
            )
            if pr_state is None:
                return (0, 0, 0, chased)
            github.post(f"issues/{pr_number}/comments", {"body": gate})
            print(f"exhausted PR #{pr_number}")
            belt().event(
                "belt.exhaustion",
                **{
                    "logfire.msg": (
                        f"#{pr_number} exhausted: no exact-head verdict after "
                        f"{len(reviewed_heads)} rounds"
                    ),
                    "pull_request": pr_number,
                    "head_sha": head_sha,
                    "round": len(reviewed_heads),
                    "max_review_rounds": MAX_REVIEW_ROUNDS,
                    "gate_comment_state": gate_state,
                    "reason": "unreviewed-head-past-bound",
                },
            )
        return (0, 0, 0, chased)
    # A seat-authored human gate holds this exact head.  An unreviewed head is
    # the belt's only evidence of a stall, and a gate produces exactly that
    # shape — no head change, no verdict — so without this the scheduled leg
    # summons a reviewer and spends a round on a head the gate has already
    # said cannot survive (sokrates#1107, round 5 of 7).
    #
    # Sited here on purpose: after the exhaustion branch and after the
    # retrospective chase, before both summon routes.  The hold withholds a
    # *reviewer*; it does not withhold the records that automation stopped,
    # which cost no round and are what a human reads next.
    if head_is_held(comments, head_sha) or head_is_skipped(comments, head_sha):
        print(
            f"held head {repository}#{pr_number} (head={head_sha}): a "
            "seat-authored human gate stands; no reviewer summoned"
        )
        return (0, 0, 0, chased)
    # A standing substitute summon owns the head in both directions: it is an
    # assignment to a seat, and recomputing ownership when the meter moves
    # would post a second reviewer against the same exact head.
    if substitute_summon_covers_head(comments, head_sha):
        return (0, 0, 0, chased)
    # A bare Codex nudge owns the head only while Codex has not refused it.
    # Treating the nudge marker as unconditional coverage is a permanent
    # stall: the refusal is (correctly) not a result, so the head never
    # enters reviewed_heads, and every scan would return here forever — the
    # exact black hole the router exists to close.
    if bare_nudge_covers_head(
        comments, head_sha
    ) and not quota_refusal_is_latest_codex_signal(reviews, comments, codex_login):
        return (0, 0, 0, chased)
    route, route_reason = find_half_route(
        reviews, comments, codex_login, usage_meter=usage_meter
    )
    meter = usage_meter if isinstance(usage_meter, Mapping) else None
    belt().event(
        "belt.find_half",
        **{
            "logfire.msg": f"#{pr_number} find half -> {route}",
            "pull_request": pr_number,
            "head_sha": head_sha,
            "route": route,
            "reason": route_reason,
            "rounds_consumed": len(reviewed_heads),
            "meter_utilization": meter["utilization"] if meter else None,
            "meter_resets_at": str(meter["resets_at"]) if meter else "",
            "codex_threshold": codex_threshold(),
        },
    )
    if route == "codex":
        if bare_nudge_covers_head(comments, head_sha):
            # Codex's refusal was superseded by later Codex activity, but the
            # standing nudge for this head was already posted — do not repeat.
            return (0, 0, 0, chased)
        if not verdict_state_held(
            github,
            pr_number=pr_number,
            head_sha=head_sha,
            codex_login=codex_login,
            snapshot=snapshot_result,
            repository=repository,
            action="review nudge",
        ):
            return (0, 0, 0, chased)
        if (
            refresh_pr_at_head(
                github,
                pr_number,
                head_sha,
                repository,
                action="review nudge",
            )
            is None
        ):
            return (0, 0, 0, chased)
        github.post(
            f"issues/{pr_number}/comments", {"body": nudge_comment_body(head_sha)}
        )
        print(f"nudged PR #{pr_number} ({route_reason})")
        belt().event(
            "belt.nudge",
            **{
                "logfire.msg": f"#{pr_number} nudged @codex at {head_sha[:12]}",
                "pull_request": pr_number,
                "head_sha": head_sha,
                "rounds_consumed": len(reviewed_heads),
                "reason": route_reason,
            },
        )
        return (1, 0, 0, chased)
    if not verdict_state_held(
        github,
        pr_number=pr_number,
        head_sha=head_sha,
        codex_login=codex_login,
        snapshot=snapshot_result,
        repository=repository,
        action="substitute review summon",
    ):
        return (0, 0, 0, chased)
    if (
        refresh_pr_at_head(
            github,
            pr_number,
            head_sha,
            repository,
            action="substitute review summon",
        )
        is None
    ):
        return (0, 0, 0, chased)
    actor = substitute_actor()
    review_round = result_round_for_head(reviewed_heads, head_sha)
    # Slack first, then the marker — the same publication rule as every
    # other wake leg.  Marker-first made a lost wake unrecoverable: a
    # Slack failure after the marker left the head "covered" with #hive
    # silent, the exact stall class this router exists to close.  With
    # Slack first, a marker failure raises out of the scan (R-3) and the
    # next tick re-summons; a duplicate summon is attention-only and the
    # seat dedupes it, which is the safe direction.
    slack = SlackApi(required_env("HIVE_BOT_TOKEN"), required_env("HIVE_CHANNEL"))
    slack.post_message(
        substitute_review_wake_message(
            actor=actor,
            reason=route_reason,
            pr_url=str(pull_request.get("html_url") or f"{repository}#{pr_number}"),
            branch=str(head.get("ref") or "unknown"),
            head_sha=head_sha,
            review_round=review_round,
            repository=repository,
        )
    )
    github.post(
        f"issues/{pr_number}/comments",
        {
            "body": substitute_summon_comment_body(
                head_sha=head_sha,
                actor=actor,
                reason=route_reason,
                review_round=review_round,
            )
        },
    )
    print(f"summoned substitute for PR #{pr_number} ({route_reason})")
    belt().event(
        "belt.substitute.summon",
        **{
            "logfire.msg": f"#{pr_number} summoned substitute `{actor}`",
            "pull_request": pr_number,
            "head_sha": head_sha,
            "substitute_actor": actor,
            "round": review_round,
            "max_review_rounds": MAX_REVIEW_ROUNDS,
            "reason": route_reason,
        },
    )
    return (0, 1, 0, chased)


def codex_review_github(repository: str) -> GitHubApi:
    """The connected-account client every reviewer summon posts through.

    Codex ignores a summon authored by ``github-actions[bot]``, so the
    credential must authenticate as the GitHub user connected to Codex cloud.
    A job wired to the wrong secret fails here, loudly, instead of summoning
    nobody in silence (R-3).
    """
    github = GitHubApi(required_env("GITHUB_TOKEN"), repository)
    expected_login = required_env("CODEX_REVIEW_AUTHOR")
    authenticated_login = github.authenticated_login()
    if authenticated_login != expected_login:
        raise RuntimeError(
            "Codex review credential authenticates as "
            f"{authenticated_login}, expected {expected_login}"
        )
    return github


def summon_on_push() -> None:
    """Reconcile one PR the moment its head moves (``pull_request: synchronize``).

    The event twin of the scheduled scan.  A repaired head needs its own round,
    and until this leg existed the only path to one was the scheduled stall
    nudge — which GitHub delivers as a multi-hour heartbeat, not a five-minute
    one: on Skrates/sokrates the ``*/5`` schedule fired at 23:22, 01:07, 05:53,
    10:00 and 13:34Z across 2026-09-05/06, so every burn round waited hours for
    a clock tick and four repaired heads sat over an hour on 09-06 with verdicts
    bound to the SHA before the repair.

    The head move is itself the proof the stall window exists to wait for, so
    the commit-age gate does not apply.  Every other decision — seat authorship,
    loop exemption, the round bound, the seat-authored hold, the meter route,
    once-per-head marker coverage — is ``_scan_open_pull``'s, unchanged: this is
    a second caller of the one summon site, not a second site.
    """
    event = load_event()
    action = str(event.get("action") or "")
    if action != "synchronize":
        print(f"ignored pull_request action {action!r}: only a head move summons")
        return
    payload = event.get("pull_request")
    if not isinstance(payload, Mapping):
        raise TypeError("event does not contain a pull request")
    pr_number = int(payload.get("number") or 0)
    repository = required_env("GITHUB_REPOSITORY")
    github = codex_review_github(repository)
    # The live record, never the payload: by the time this run executes the
    # head may have moved again, and ``refresh_pr_at_head`` guards the post.
    pull_request = github.get(f"pulls/{pr_number}")
    if str(pull_request.get("state")) != "open":
        print(f"ignored head move on non-open PR #{pr_number}")
        return
    if not head_is_same_repo(pull_request):
        # A fork head carries no secrets on this event and the seat gate inside
        # the scan skips it regardless; name the reason rather than fail cold.
        print(f"ignored head move on fork PR #{pr_number}")
        return
    head_sha = str(pull_request.get("head", {}).get("sha") or "")
    if record_review_skip(github, pull_request, pr_number=pr_number, head_sha=head_sha):
        # The seat has said this head needs no round. Nothing else the scan
        # does on a fresh push applies (no verdict to redeliver, no chase), and
        # the scheduled leg reads the marker as a disposition from here on.
        print(f"push-routed PR #{pr_number} (skipped by the pushing seat's trailer)")
        return
    codex_login = os.environ.get("CODEX_LOGIN", CODEX_LOGIN)
    # Read the meter here and hand it down, as the scheduled scan does: the
    # router would fetch it itself, but the scan only serialises a reading it
    # was GIVEN into the find-half telemetry, so a sentinel here exports every
    # push-path routing decision as if no meter supported it.
    nudged, summoned, redelivered, chased = _scan_open_pull(
        github,
        pull_request,
        repository=repository,
        codex_login=codex_login,
        now=datetime.now(timezone.utc),
        usage_meter=usage_meter_reading(),
        stall_gate=False,
    )
    print(
        f"push-routed PR #{pr_number} "
        f"(nudged={nudged}, summoned={summoned}, redelivered={redelivered}, "
        f"chased={chased})"
    )


def record_review_skip(
    github: Any, pull_request: Mapping[str, Any], *, pr_number: int, head_sha: str
) -> bool:
    """Post the ``skip`` disposition when the pushed head asks for it; True when posted.

    Read from the head commit's message on the push leg only — the one moment
    the seat's decision and the head it applies to are the same object. The
    scan that follows sees the marker and withholds the reviewer, exactly as it
    does for a hold; a head already skipped is not re-marked.
    """
    if not head_sha:
        return False
    commit = github.get(f"commits/{head_sha}")
    message = ""
    if isinstance(commit, Mapping):
        inner = commit.get("commit")
        if isinstance(inner, Mapping):
            message = str(inner.get("message") or "")
    reason = review_skip_reason(message)
    if reason is None:
        return False
    comments = github.paginate(f"issues/{pr_number}/comments")
    if head_is_skipped(comments, head_sha):
        print(f"PR #{pr_number}: head {head_sha[:8]} already carries a skip marker")
        return False
    github.post(
        f"issues/{pr_number}/comments", {"body": skip_comment_body(head_sha, reason)}
    )
    print(f"PR #{pr_number}: review round skipped at {head_sha[:8]} — {reason}")
    return True


def nudge_stalled_reviews() -> None:
    repository = required_env("GITHUB_REPOSITORY")
    codex_login = os.environ.get("CODEX_LOGIN", CODEX_LOGIN)
    github = codex_review_github(repository)
    now = datetime.now(timezone.utc)
    usage_meter = usage_meter_reading()
    belt().event(
        "belt.meter",
        **{
            "logfire.msg": (
                "AI-usage meter absent"
                if usage_meter is None
                else f"AI-usage Codex pool at {usage_meter['utilization']:.2f}"
            ),
            "meter_present": usage_meter is not None,
            "meter_utilization": (
                usage_meter["utilization"] if usage_meter is not None else None
            ),
            "meter_resets_at": (
                str(usage_meter["resets_at"]) if usage_meter is not None else ""
            ),
            "codex_threshold": codex_threshold(),
        },
    )
    nudged = 0
    summoned = 0
    redelivered = 0
    chased = 0
    errors: list[tuple[int, Exception]] = []
    scanned = 0
    for pull_request in github.paginate("pulls", query={"state": "open"}):
        pr_number = int(pull_request.get("number") or 0)
        scanned += 1
        try:
            (
                nudged_delta,
                summoned_delta,
                redelivered_delta,
                chased_delta,
            ) = _scan_open_pull(
                github,
                pull_request,
                repository=repository,
                codex_login=codex_login,
                now=now,
                usage_meter=usage_meter,
            )
        except Exception as error:  # noqa: BLE001 - one PR must not blind the rest.
            print(
                f"scan failed for {repository}#{pr_number}: "
                f"{type(error).__name__}: {error}",
                file=sys.stderr,
            )
            errors.append((pr_number, error))
            continue
        nudged += nudged_delta
        summoned += summoned_delta
        redelivered += redelivered_delta
        chased += chased_delta
    # The loop above is the only enumeration of open PRs, so it is also the only
    # place a retrospective request can be seen — until the PR closes, which the
    # exhaustion gate invites a human to do while the delivery window is running.
    closed_chased = 0
    try:
        closed_chased, closed_errors = chase_closed_pull_retrospectives(
            github, repository=repository, now=now
        )
        errors.extend(closed_errors)
    except Exception as error:  # noqa: BLE001 - the open-PR pass is already done.
        # Enumerating closures is the last thing this scan does, and failing it
        # must not discard the summary and telemetry the pass above earned.
        print(
            f"closed-PR retrospective sweep failed for {repository}: "
            f"{type(error).__name__}: {error}",
            file=sys.stderr,
        )
        errors.append((0, error))
    chased += closed_chased
    print(
        f"nudge scan complete (nudged={nudged}, substitute={summoned}, "
        f"redelivered={redelivered}, retrospectives chased={chased}, "
        f"{closed_chased} on PRs closed in the last "
        f"{RETROSPECTIVE_CLOSED_SWEEP_HOURS}h)"
    )
    belt().event(
        "belt.scan.complete",
        **{
            "logfire.msg": (
                f"scan: {scanned} open PR(s), {nudged} nudged, "
                f"{summoned} summoned, {redelivered} re-delivered, "
                f"{chased} retrospective(s) chased"
            ),
            "pull_requests_scanned": scanned,
            "nudged": nudged,
            "summoned": summoned,
            "redelivered": redelivered,
            "retrospectives_chased": chased,
            "scan_errors": len(errors),
        },
    )
    if errors:
        raise ScanCompletedWithErrors("nudge", errors)


def send_canary() -> None:
    repository = required_env("GITHUB_REPOSITORY")
    run_id = required_env("GITHUB_RUN_ID")
    slack = SlackApi(required_env("HIVE_BOT_TOKEN"), required_env("HIVE_CHANNEL"))
    actor = burn_actor()
    slack.post_message(
        f"WAKE: {actor}\n\n"
        "Review-loop burn-seat canary - no PR and no code changes. This is a "
        "controlled GitHub Actions -> Slack -> Hive -> burn-seat probe. "
        "Reply in this thread with exactly `REVIEW-LOOP CANARY OK`, your "
        "current weave-doctrine short commit if this seat holds a checkout, "
        "and whether your edge is healthy. Do not modify anything or print "
        "secrets.\n\n"
        f"Source: `{repository}` workflow run `{run_id}`."
    )
    print(f"posted review-loop canary for {repository} run {run_id}")
    belt().event(
        "belt.canary",
        **{
            "logfire.msg": f"canary woke `{actor}`",
            "burn_actor": actor,
            "github_run_id": run_id,
        },
    )


def skill_audit_actor() -> str:
    """The seat the weekly skill audit wakes; same grammar as every actor."""
    raw = os.environ.get("SKILL_AUDIT_ACTOR", "").strip() or DEFAULT_SKILL_AUDIT_ACTOR
    actor = normalize_substitute_actor(raw)
    if actor is None:
        raise ValueError(
            f"SKILL_AUDIT_ACTOR={raw!r} is outside the actor grammar "
            "[a-z0-9-]+ after normalization; refusing to wake an "
            "unroutable audit seat"
        )
    return actor


def skills_changed_since(github: GitHubApi, since: datetime) -> bool:
    """True when any commit in the window touched a skill corpus root.

    The commits API takes one ``path`` per query, so each root is asked
    separately; the first non-empty answer suffices.
    """
    since_param = since.strftime("%Y-%m-%dT%H:%M:%SZ")
    for root in SKILL_PATH_PREFIXES:
        commits = github.get(
            "commits",
            query={"since": since_param, "path": root.rstrip("/"), "per_page": 1},
        )
        if isinstance(commits, list) and commits:
            return True
    return False


def _skill_audit_run_started(run: Mapping[str, Any]) -> datetime | None:
    raw = run.get("created_at")
    if not isinstance(raw, str) or not raw.strip():
        return None
    try:
        parsed = parse_github_time(raw.strip())
    except ValueError:
        return None
    return parsed.replace(tzinfo=timezone.utc) if parsed.tzinfo is None else parsed


def skill_audit_window_start(
    github: GitHubApi,
    *,
    now: datetime,
    current_run_id: str,
) -> tuple[datetime, str]:
    """Start the window at the previous successful skill-audit run.

    The routine's own run record is the watermark: no Slack history, no
    committed marker, no second store to drift.  A run that failed never
    advances it, so a failure widens the next window instead of dropping the
    skill commits it missed.  A successful run that posted nothing is still
    coverage — it looked and found no skill-corpus commits.  Overlap is the
    safe direction: a commit audited twice is noise, a commit audited never
    is the hole this exists to close.
    """
    page = 1
    per_page = 100
    try:
        while True:
            payload = github.get(
                f"actions/workflows/{SKILL_AUDIT_WORKFLOW_FILE}/runs",
                query={"status": "success", "per_page": per_page, "page": page},
            )
            entries = (
                payload.get("workflow_runs") if isinstance(payload, Mapping) else None
            )
            if not isinstance(entries, list) or not entries:
                break
            for run in entries:
                if not isinstance(run, Mapping):
                    continue
                if str(run.get("id")) == str(current_run_id):
                    continue
                started = _skill_audit_run_started(run)
                if started is not None:
                    return started, "previous successful skill-audit run"
            if len(entries) < per_page:
                break
            page += 1
    except ApiHttpError as error:
        if error.status_code != 404:
            raise
    return (
        now - timedelta(days=SKILL_AUDIT_FALLBACK_DAYS),
        f"{SKILL_AUDIT_FALLBACK_DAYS}-day fallback — no previous successful run",
    )


def send_skill_audit(*, now: datetime | None = None) -> None:
    """Post the weekly one-pass skill-audit wake, or say why not.

    Skills are exempt from the per-PR review loop (Hákon's ruling,
    2026-08-21); this single weekly pass is their entire quality gate. A
    quiet window posts nothing — a wake with no possible work is noise.
    The lookback is the previous successful run of this workflow, not a
    fixed number of days, so a delayed or dropped schedule cannot leave
    skill commits between two consecutive windows.
    """
    repository = required_env("GITHUB_REPOSITORY")
    github = GitHubApi(required_env("GITHUB_TOKEN"), repository)
    moment = datetime.now(timezone.utc) if now is None else now
    since, source = skill_audit_window_start(
        github, now=moment, current_run_id=current_run_id()
    )
    since_stamp = since.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%MZ")
    now_stamp = moment.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%MZ")
    if not skills_changed_since(github, since):
        print(
            f"no skill-corpus commits in {repository} since "
            f"{since_stamp} ({source}) - skipping the audit wake"
        )
        return
    slack = SlackApi(required_env("HIVE_BOT_TOKEN"), required_env("HIVE_CHANNEL"))
    actor = skill_audit_actor()
    roots = ", ".join(f"`{root}`" for root in SKILL_PATH_PREFIXES)
    slack.post_message(
        f"WAKE: {actor}\n\n"
        "Weekly skill audit - one pass, no review loop. Skill files are "
        "exempt from per-PR Codex review (Hákon's ruling, 2026-08-21); this "
        "audit is their entire quality gate.\n\n"
        f"Repo: `{repository}`. Audit every skill file under {roots} "
        f"changed since {since_stamp} "
        f"({source}; window {since_stamp} → {now_stamp}) "
        "(`git log --since` over those roots on the default branch), judged "
        "once against `writing-skills`. Land repairs as direct commits or "
        "follow-up tickets. One pass means one pass: no re-review, no burn "
        "rounds, no verdict comments.\n\n"
        "Reply in this thread with the files audited and what changed."
    )
    print(f"posted weekly skill-audit wake for {repository} to {actor}")
    belt().event(
        "belt.skill_audit",
        **{
            "logfire.msg": f"weekly skill audit woke `{actor}`",
            "audit_actor": actor,
            "window_since": since_stamp,
            "window_until": now_stamp,
            "window_source": source,
        },
    )


def _parse_stamp(raw: Any) -> datetime | None:
    """A GitHub timestamp, or ``None`` when missing or unparseable."""
    if not isinstance(raw, str) or not raw.strip():
        return None
    try:
        parsed = parse_github_time(raw.strip())
    except ValueError:
        return None
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return parsed


def _item_edit_time(item: Mapping[str, Any]) -> datetime | None:
    """When the item's current body last changed, if GitHub exposes that clock.

    REST issue and review comments carry ``updated_at``. REST pull-request
    reviews do not; GraphQL ``lastEditedAt`` (copied onto the review, or
    present under that name) is the same clock on that channel.
    """
    for key in _EDIT_STAMP_KEYS:
        parsed = _parse_stamp(item.get(key))
        if parsed is not None:
            return parsed
    return None


def _edit_clock_proves_an_edit(
    item: Mapping[str, Any], edited: datetime | None, when: datetime | None
) -> bool:
    """True when GitHub's clocks prove the current body is not the original.

    GraphQL ``lastEditedAt`` is omitted on a never-edited review, so a
    parseable value is the proof even when it equals ``submitted_at``
    (submit and edit sharing a whole second). REST comment ``updated_at``
    is always present, so the proof there is that it differs from the
    creation stamp.
    """
    if _parse_stamp(item.get("lastEditedAt") or item.get("last_edited_at")) is not None:
        return True
    return edited is not None and when is not None and edited != when


def _edit_is_after_closure(
    item: Mapping[str, Any], when: datetime | None, boundary: datetime
) -> bool:
    """True when the current body is not the body as of ``boundary``.

    GitHub timestamps are whole seconds.  An item edited in the close or
    merge second compares equal to the boundary under a strict ``>`` and
    would keep the current body.  Equality with the boundary is therefore
    not-as-of-closure when the clocks prove an edit.
    """
    edited = _item_edit_time(item)
    if edited is None:
        return False
    if edited > boundary:
        return True
    return edited == boundary and _edit_clock_proves_an_edit(item, edited, when)


def _with_untrusted_body(item: Mapping[str, Any]) -> dict[str, Any]:
    """Keep identity; the current body is not as-of-closure evidence."""
    return {**item, "body": "", BODY_AS_OF_CLOSURE: False}


def with_review_edit_times(
    github: GitHubApi, pr_number: int, reviews: Sequence[Any]
) -> list[Any]:
    """Copy GraphQL ``lastEditedAt`` onto REST reviews as ``updated_at``.

    ``lastEditedAt`` is kept too: it is omitted unless the review was
    edited, which is the proof ``at_closure`` needs when that clock equals
    ``submitted_at``.  Test stand-ins that do not implement
    ``review_last_edited_at`` are left unchanged; they can still put
    ``lastEditedAt`` on the review object for ``at_closure`` to read.
    """
    fetch = getattr(github, "review_last_edited_at", None)
    if not callable(fetch):
        return list(reviews)
    times = fetch(pr_number)
    if not isinstance(times, Mapping) or not times:
        return list(reviews)
    enriched: list[Any] = []
    for item in reviews:
        if not isinstance(item, Mapping):
            enriched.append(item)
            continue
        if _parse_stamp(item.get("updated_at")) is not None:
            enriched.append(item)
            continue
        node_id = item.get("node_id")
        review_id = item.get("id")
        edited = None
        if isinstance(node_id, str) and node_id in times:
            edited = times[node_id]
        elif review_id in times:
            edited = times[review_id]
        if _parse_stamp(edited) is None:
            enriched.append(item)
            continue
        # Keep ``lastEditedAt`` as well as ``updated_at``.  Copying only the
        # REST key would collapse GraphQL's "present iff edited" clock into
        # comment ``updated_at`` (always present), and a submit-and-edit in
        # the close second would then look never-edited.
        enriched.append({**item, "updated_at": edited, "lastEditedAt": edited})
    return enriched


def reviews_as_of_closure(
    github: GitHubApi, pr_number: int, closed_at: str
) -> list[Any]:
    """Reviews in the closure snapshot, with REST's missing edit clock filled in.

    Both terminal readers use this so a GraphQL enrichment cannot apply at
    one cut and not the other.  An open PR has no boundary, so the extra
    fetch is skipped.
    """
    reviews = github.paginate(f"pulls/{pr_number}/reviews")
    if closed_at:
        reviews = with_review_edit_times(github, pr_number, reviews)
    return at_closure(reviews, closed_at, "submitted_at")


def at_closure(items: Sequence[Any], closed_at: str, *stamp_keys: str) -> list[Any]:
    """Only the thread items that existed when the PR reached ``closed_at``.

    One definition for both terminal readers.  The belt summary and the merge
    digest each describe a moment the thread has since moved past, and a
    disagreement about where that moment cuts would make them report different
    histories for the same PR — which is the disagreement everything else here
    is built to prevent.

    An empty ``closed_at`` means there is no boundary to measure against — an
    open PR is current, and every item is kept.  An item whose own timestamp is
    missing or unparseable is kept for the same reason the result stream sorts
    it first: an undated event is not evidence that it arrived after the
    closure.  The first ``stamp_keys`` entry that parses is the item's time.

    GitHub returns a comment's CURRENT body.  An item whose edit clock
    (``updated_at``, or ``lastEditedAt`` on a pull-request review) is later
    than the boundary is therefore not as-of-closure, even when ``created_at``
    (or another stamp in ``stamp_keys``) is earlier: trusting that body would
    let a post-closure edit rewrite the snapshot's rounds, findings and
    exhaustion.  The original body is not recoverable from the API, so it is
    cleared and marked ``body_as_of_closure=False``.  The item itself is
    kept: dropping it unbinds pre-closure inline comments from their review
    and lets a clean-looking summary reclassify a findings round as CLEAN.

    GitHub timestamps are whole seconds.  An edit in the same second as close
    or merge compares equal to the boundary under a strict ``>`` and would
    keep the current body.  When the clocks prove an edit — GraphQL
    ``lastEditedAt`` is present, or the REST edit clock differs from the
    creation stamp — equality with the boundary is treated as
    not-as-of-closure.
    """
    if not closed_at:
        return list(items)
    boundary = result_event_time(closed_at)
    kept: list[Any] = []
    for item in items:
        if not isinstance(item, Mapping):
            continue
        when = None
        for key in stamp_keys:
            parsed = _parse_stamp(item.get(key))
            if parsed is not None:
                when = parsed
                break
        if when is not None and when > boundary:
            continue
        if _edit_is_after_closure(item, when, boundary):
            kept.append(_with_untrusted_body(item))
            continue
        kept.append(item)
    return kept


def pr_belt_summary(
    github: GitHubApi,
    pull_request: Mapping[str, Any],
    codex_login: str,
) -> dict[str, Any]:
    """The whole-PR belt outcome, read from the PR's own review thread.

    One definition of a round serves both the live terminal emission and the
    offline baseline (``bin/review_loop_backfill.py``), so history and
    instrument cannot disagree about what they are counting.  Every field is
    derived from the same parsers the router routes on.

    This describes a CLOSURE, so it is measured as of ``closed_at`` rather than
    as of now.  A review, clean comment, substitute marker or exhaustion gate
    posted after a PR closed — a reopened thread, a rerun terminal workflow, a
    queued Codex review that landed late, a backfill run months afterwards —
    is a fact about the thread today, not about the belt state the closure
    reached.  Folded in, it moves that closure's rounds, findings, CLEAN and
    exhaustion after the event it claims to describe.  Every parser below is
    therefore fed the thread as it stood at closure.

    ``loop_exempt`` is the SNAPSHOT fact: every path the PR touches sits under
    a loop-exempt corpus root today.  ``belt_exempt`` is the measurement
    decision, and the two are not the same question.  Every routing path skips
    a loop-exempt PR because the corpus's own gate owns its whole quality bar,
    so such a PR has no rounds by design and, measured without the exemption,
    reads as a belt failure — a never-reviewed, never-CLEAN outcome.  But a PR
    that took real belt rounds and only then reverted its non-corpus files
    closes with an exempt snapshot and a genuine history; exempting it on the
    snapshot alone deletes rounds and findings the belt really spent.  Recorded
    history is what settles it: the exemption holds only where there is none.
    Both fields are reported rather than dropped so each consumer excludes
    visibly.
    """
    pr_number = int(pull_request["number"])
    head = pull_request.get("head")
    head_sha = str(head["sha"]) if isinstance(head, Mapping) else ""
    closed_at = str(pull_request.get("closed_at") or "")
    reviews = reviews_as_of_closure(github, pr_number, closed_at)
    conversation = at_closure(
        github.paginate(f"issues/{pr_number}/comments"), closed_at, "created_at"
    )
    # Inline comments carry their own clock.  Selecting them by their review's
    # id excludes every comment of a post-closure *review*, but a late comment
    # filed — or replied to — under a review submitted BEFORE closure passes
    # that filter untouched, and then decides the verdict: ``codex_result_events``
    # gives owned inline findings precedence over a clean summary, so one
    # comment arriving after the PR closed retroactively turns the review that
    # closed it into a findings round, and ``round_history`` publishes the late
    # location and severity with it.  The merge digest already cuts this
    # collection at ``merged_at``; both terminal readers cut it the same way.
    review_comments = at_closure(
        github.paginate(f"pulls/{pr_number}/comments"), closed_at, "created_at"
    )
    events = codex_result_events(
        github,
        reviews,
        conversation,
        codex_login,
        pr_number=pr_number,
        review_comments=review_comments,
    )
    reviewed_heads = result_heads_from_events(events)
    history = round_history(
        reviewed_heads,
        reviews,
        review_comments,
        codex_login,
        latest_results=latest_result_by_head(events),
        issue_comments=conversation,
    )
    # ``closed_review``, not a CLEAN prefix on the rendered verdict: a clean
    # comment whose reviewed commit no longer resolves renders as CLEAN and
    # establishes no closure, so a prose test reports review as closed on a
    # head the helper could not even identify.  The round still counts toward
    # ``rounds`` — it was consumed — it just cannot be the one that closed.
    rounds_to_clean = next(
        (int(entry["round"]) for entry in history if entry["closed_review"]),
        None,
    )
    # The files endpoint answers about the PR's diff TODAY; there is no
    # as-of-closure file list to read.  That is why the snapshot alone cannot
    # carry the exemption, and why ``history`` — which is measured at closure —
    # is the half that decides it.
    loop_exempt = loop_exempt_pr(github, pr_number, closed_at=closed_at)
    resolved = (
        author_for_pr(github, pr_number, head_sha, pull_request) if head_sha else None
    )
    # The list endpoint carries ``merged_at`` but no ``merged`` field, and it
    # keeps a ``merge_commit_sha`` for closed-unmerged PRs (the last test
    # merge). Reading either one alone reports every backfilled PR as
    # unmerged, or hands an abandoned PR a landed SHA.
    merged = bool(pull_request.get("merged") or pull_request.get("merged_at"))
    # Recurrence counts ROUNDS a site appeared in, so a site named twice in one
    # round is one appearance, not a repeat.
    rounds_by_site: dict[str, int] = {}
    rounds_by_path: dict[str, int] = {}
    for entry in history:
        sites = {location_site(str(item)) for item in entry["locations"]}
        for site in sites:
            rounds_by_site[site] = rounds_by_site.get(site, 0) + 1
        for path in {site.split(":", 1)[0] for site in sites}:
            rounds_by_path[path] = rounds_by_path.get(path, 0) + 1
    return {
        "pull_request": pr_number,
        "head_sha": head_sha,
        "loop_exempt": loop_exempt,
        # The exemption, not the snapshot: a PR the belt really reviewed keeps
        # its rounds even if its final diff reverted to exempt-corpus files.
        "belt_exempt": loop_exempt and not history,
        "author": resolved[0] if resolved else "",
        "author_seat": resolved[1] if resolved else "",
        "rounds": len(history),
        "rounds_to_clean": rounds_to_clean,
        "findings_total": sum(int(entry["counts"]["total"]) for entry in history),
        "findings_p1": sum(int(entry["counts"]["p1"]) for entry in history),
        "findings_p2": sum(int(entry["counts"]["p2"]) for entry in history),
        "findings_p3": sum(int(entry["counts"]["p3"]) for entry in history),
        "round_heads": [str(entry["head"]) for entry in history],
        "round_findings": [int(entry["counts"]["total"]) for entry in history],
        "round_verdicts": [str(entry["verdict"]) for entry in history],
        "round_locations": [
            [str(item) for item in entry["locations"]] for entry in history
        ],
        # Recurrence, at two grains.  An exact SITE (path:line) repeating is
        # repair that did not stick; a FILE repeating across rounds is the
        # coarser signal that survives the line drift every burn causes, and it
        # is the one "did the same file keep coming back" asks for.  Neither
        # grain compares the rendered identity: Codex rewords a returning
        # finding freely, and a reworded title is not a cured site.
        "repeated_locations": sorted(
            site for site, seen in rounds_by_site.items() if seen > 1
        ),
        "repeated_paths": sorted(
            path for path, seen in rounds_by_path.items() if seen > 1
        ),
        # Any head's gate, at any policy: the PR reached the bound at least
        # once.  The bound it reached is recorded by the marker itself and is
        # absent when only a legacy unversioned marker gated it — today's
        # MAX_REVIEW_ROUNDS is not evidence about a gate posted under an
        # earlier policy.
        "exhausted": exhaustion_gate_recorded(conversation),
        "exhausted_max_rounds": exhaustion_marker_bound(conversation),
        "merged": merged,
        "merged_sha": str(pull_request.get("merge_commit_sha") or "") if merged else "",
        "created_at": str(pull_request.get("created_at") or ""),
        "closed_at": str(pull_request.get("closed_at") or ""),
        "title": str(pull_request.get("title") or ""),
        "url": str(pull_request.get("html_url") or ""),
    }


def closure_event_id(repository: str, summary: Mapping[str, Any]) -> str:
    """The closure this span describes, independent of what emitted it.

    OTLP mints a fresh trace and span id per export, so a rerun of the
    ``belt-terminal`` job — after a sibling job failed, say — writes a second,
    indistinguishable ``belt.terminal`` row for one closure and doubles that PR
    in any ``count(*)`` convergence query.  This names the closure event
    itself, so a dashboard reduces to one row per closure no matter how many
    times the job ran.
    """
    return f"{repository}#{summary['pull_request']}@{summary['closed_at']}"


def route_pull_request_closed(event: Mapping[str, Any] | None = None) -> None:
    """Emit one terminal belt span when a seat-authored PR closes.

    The per-round spans say what each round cost; this says what the whole PR
    cost — rounds to CLEAN, findings burned, whether the bound was reached,
    and the SHA that actually landed.  It routes nothing and wakes nobody.

    The emission is not idempotent — a push exporter cannot be — so it carries
    a stable ``closure_event`` id instead and the dashboard queries deduplicate
    on it.

    With no sink the command returns before reading anything.  Collecting the
    summary costs several GitHub reads, and this job exists only to export
    them: on the no-token path — the documented default for an adopting
    repository — a transient 5xx or a token without the scope to read the
    review thread would turn a job that measures nothing into a red one.
    """
    if not belt().enabled:
        print("belt telemetry disabled: no terminal span, nothing collected")
        return
    event = event or load_event()
    pull_request = event.get("pull_request")
    if not isinstance(pull_request, Mapping):
        raise TypeError("event does not contain a pull_request")
    repository = required_env("GITHUB_REPOSITORY")
    codex_login = os.environ.get("CODEX_LOGIN", CODEX_LOGIN)
    github = GitHubApi(required_env("GITHUB_TOKEN"), repository)
    emit_terminal_span(github, repository, pull_request, codex_login)


def emit_terminal_span(
    github: GitHubApi,
    repository: str,
    pull_request: Mapping[str, Any],
    codex_login: str,
) -> None:
    """Export one closure's belt outcome, or record why it was not exported.

    Shared by the closure event and the scheduled fork sweep so both emit the
    same span from the same summary — an outcome that differed by which path
    observed it would be a measurement of the paths, not of the belt.
    """
    summary = pr_belt_summary(github, pull_request, codex_login)
    if not summary["author_seat"]:
        print(f"non-seat author on closed {repository}#{summary['pull_request']}")
        belt_ignored("non-seat-author", pull_request=summary["pull_request"])
        return
    if summary["belt_exempt"]:
        # Every routing path exempts a loop-exempt PR, so it has no rounds by
        # construction.  Emitting it here would enter a zero-round, no-CLEAN
        # outcome into the convergence distribution for a PR the belt was
        # never supposed to review.  Recorded as an ignored route, not dropped.
        # An exempt snapshot over a real round history is NOT this case: the
        # belt reviewed it, and its convergence outcome is the instrument's.
        print(f"loop-exempt PR {repository}#{summary['pull_request']} - belt exempt")
        belt_ignored("loop-exempt", pull_request=summary["pull_request"])
        return
    belt().event(
        "belt.terminal",
        **{
            "logfire.msg": (
                f"#{summary['pull_request']} closed after {summary['rounds']} "
                f"round(s), {summary['findings_total']} finding(s)"
            ),
            "pull_request": summary["pull_request"],
            # The closure, not the emission: a rerun of this job repeats the
            # row and every convergence query groups on this to collapse it.
            "closure_event": closure_event_id(repository, summary),
            "closed_at": summary["closed_at"],
            "head_sha": summary["head_sha"],
            "author_seat": summary["author_seat"],
            "rounds": summary["rounds"],
            "rounds_to_clean": summary["rounds_to_clean"],
            "findings_total": summary["findings_total"],
            "findings_p1": summary["findings_p1"],
            "findings_p2": summary["findings_p2"],
            "findings_p3": summary["findings_p3"],
            "round_findings": summary["round_findings"],
            "repeated_locations": summary["repeated_locations"][:FINDING_SPAN_BUDGET],
            "repeated_location_count": len(summary["repeated_locations"]),
            "repeated_paths": summary["repeated_paths"][:FINDING_SPAN_BUDGET],
            "repeated_path_count": len(summary["repeated_paths"]),
            "exhausted": summary["exhausted"],
            # The bound that produced the gate, read off the marker that posted
            # it — not the bound configured today.  Absent when a legacy
            # unversioned marker gated the PR: the policy it ran under was
            # never recorded, and an unmeasured bound must stay unmeasured.
            # The policy in force at emission rides the invocation root span in
            # this same trace, which is the only place it is evidence.
            "exhausted_max_rounds": summary["exhausted_max_rounds"],
            "merged": summary["merged"],
            "merged_sha": summary["merged_sha"],
        },
    )
    print(
        f"belt terminal for {repository}#{summary['pull_request']} "
        f"(rounds={summary['rounds']}, findings={summary['findings_total']}, "
        f"merged={summary['merged']})"
    )


def fork_originated(pull_request: Mapping[str, Any], repository: str) -> bool:
    """True when this PR's head branch lives outside the base repository.

    A deleted head repository reads as absent rather than as same-repo: the
    branch is provably not in the base repo (the base repo's own branches are
    never reported with a null ``repo``), and treating the unknown case as
    same-repo is what would drop it from the sweep silently.
    """
    head = pull_request.get("head")
    if not isinstance(head, Mapping):
        return False
    head_repo = head.get("repo")
    if not isinstance(head_repo, Mapping):
        return True
    return str(head_repo.get("full_name") or "").lower() != repository.lower()


def route_terminal_sweep() -> None:
    """Emit terminal spans for closures the ``pull_request`` event cannot.

    A ``pull_request`` event on a fork-originated PR carries no repository
    secrets — the limitation ``announce-machine-merge`` already declares for
    the merge digest — so ``belt-terminal`` runs with an empty ``LOGFIRE_TOKEN``
    and exports nothing.  Without a backstop every fork closure is missing from
    the distribution the belt advertises as live, and the gap is invisible: an
    absent span and a PR that never closed read the same.  This leg runs on the
    schedule, in the base repository's own context, where the token exists.

    Re-emission is safe by construction.  The span carries ``closure_event`` —
    the identity of the closure rather than of the export — and every
    convergence query groups on it, so a sweep that overlaps a closure event
    that did succeed collapses into one row instead of doubling the PR.  That
    is why the sweep does not try to detect which closures were exported: the
    detection would need a second store, and the dedup already holds.

    The window is generous on purpose.  The schedule is throttled by GitHub
    under load, and a leg that assumed its own cadence would silently skip
    every closure that fell between two runs.
    """
    if not belt().enabled:
        print("belt telemetry disabled: no terminal sweep, nothing collected")
        return
    repository = required_env("GITHUB_REPOSITORY")
    codex_login = os.environ.get("CODEX_LOGIN", CODEX_LOGIN)
    github = GitHubApi(required_env("GITHUB_TOKEN"), repository)
    horizon = datetime.now(timezone.utc) - timedelta(hours=BELT_SWEEP_WINDOW_HOURS)
    swept = 0
    scanned = 0
    errors: list[tuple[int, Exception]] = []
    page = 1
    # Paged by hand rather than through ``paginate``, which materializes every
    # page before returning: the stop condition below is what bounds this scan
    # to the window, and it can only bound a stream it is reading.
    while True:
        batch = github.get(
            "pulls",
            query={
                "state": "closed",
                "sort": "updated",
                "direction": "desc",
                "per_page": 100,
                "page": page,
            },
        )
        if not isinstance(batch, list) or not batch:
            break
        stop = False
        for pull_request in batch:
            scanned += 1
            # Closing a PR updates it, so ``updated_at >= closed_at``: once the
            # update stream has fallen past the horizon, no later row can be a
            # closure inside the window.
            if result_event_time(pull_request.get("updated_at")) < horizon:
                stop = True
                break
            if result_event_time(
                pull_request.get("closed_at")
            ) < horizon or not fork_originated(pull_request, repository):
                continue
            # One unsummarizable closure — a deleted fork whose head commit
            # 404s under ``author_for_pr``, say — must not abort the pass.
            # The window is time-bounded, not cursor-bounded, so an abort
            # re-skips every eligible closure *after* the poisoned row on
            # every retry until that row ages out seven days later.
            number = int(pull_request.get("number") or 0)
            try:
                emit_terminal_span(github, repository, pull_request, codex_login)
            except Exception as error:  # noqa: BLE001 - one closure, not the pass.
                print(
                    f"terminal sweep failed for {repository}#{number}: "
                    f"{type(error).__name__}: {error}",
                    file=sys.stderr,
                )
                errors.append((number, error))
                continue
            swept += 1
        if stop or len(batch) < 100:
            break
        page += 1
    print(
        f"belt terminal sweep for {repository}: {swept} fork closure(s) of "
        f"{scanned} row(s) scanned in the last {BELT_SWEEP_WINDOW_HOURS}h"
        + (f", {len(errors)} failed" if errors else "")
    )
    if errors:
        raise ScanCompletedWithErrors("terminal", errors)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "command",
        choices=(
            "route",
            "push",
            "nudge",
            "canary",
            "skill-audit",
            "terminal",
            "terminal-sweep",
            "substitute-verdict",
        ),
    )
    parser.add_argument(
        "--head",
        help="substitute-verdict: the full head SHA to read the verdict for; "
        "comment pages arrive on stdin",
    )
    args = parser.parse_args(argv)
    if args.command == "substitute-verdict":
        # A seat's read, not a belt invocation: no telemetry root, no event.
        if not args.head:
            parser.error("substitute-verdict requires --head <sha>")
        report_substitute_verdict(args.head, json.load(sys.stdin), sys.stdout)
        return 0
    telemetry = install_belt_telemetry(BeltTelemetry.from_env(args.command))
    try:
        with telemetry.span(
            # Invocation roots live in their own namespace.  ``belt.nudge``,
            # ``belt.canary`` and ``belt.terminal`` are also the names of the
            # ACTIONS those commands emit, so sharing the root's name makes a
            # scan that nudged nobody report one nudge, and a scan that nudged
            # N report N+1.  One name, one grain.
            f"belt.invocation.{args.command}",
            **{
                "logfire.msg": (
                    f"belt {args.command} {telemetry.repository or 'unknown-repo'}"
                ),
                "belt_command": args.command,
                "belt_fingerprint": script_fingerprint(),
                "github_event": os.environ.get("GITHUB_EVENT_NAME", ""),
                "github_run_id": telemetry.run_id,
                "max_review_rounds": MAX_REVIEW_ROUNDS,
            },
        ):
            {
                "route": route_codex_result,
                "push": summon_on_push,
                "nudge": nudge_stalled_reviews,
                "canary": send_canary,
                "skill-audit": send_skill_audit,
                "terminal": route_pull_request_closed,
                "terminal-sweep": route_terminal_sweep,
            }[args.command]()
    except Exception as error:  # noqa: BLE001 - CLI boundary must terminalize visibly.
        print(f"review-loop {args.command} failed: {error}", file=sys.stderr)
        return 1
    finally:
        # After the root span closes, so the invocation's own duration and
        # status ride the same export as the decisions inside it.
        telemetry.flush()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
