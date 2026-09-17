#!/usr/bin/env python3
"""Machine-merge digest — the retrospective human word over machine merges.

KRA-1074 A1 moved Hákon's merge word from prospective to retrospective: the
composed boundary (exact-head CLEAN, findings burned, green required checks, no
conflicts, Theoros at the exhaustion gate) admits the merge, and the human reads
afterwards.  This helper is the reading surface, in the two cadences A1's rider
fixed:

``announce``
    One substance line to ``#hive`` at merge time, from the merging repository's
    own workflow.  Says what the change *does* — the one thing a green tick
    cannot carry — plus its revert anchor.  Claims no reversal cost: at merge
    time nothing has been measured.
``digest``
    The scheduled cross-repo rollup.  Every repository in ``weave-repos.json``
    is reported: entries, an explicit zero, or a loud read failure.  Each entry
    carries what the change does, why, what gated it (reported, never
    re-derived), and what reversing it would cost *right now* — measured by
    attempting the revert, not guessed from a proxy.

What this is not: a re-verification of the gates, a second evidence store, and
above all not a veto window.  The veto never expires — Hákon owns the
repositories.  What the digest preserves is the *cheap* option, by putting the
account in front of him while a revert is still one command.

The gate half of every entry is read through ``review_loop`` — the same
resolution the review-loop hook publishes.  Two audit trails that can disagree
are worse than one, so this file contains no second implementation of exact-head
verdict resolution, finding counts, round numbering, or exhaustion.

Standard library only, like its sibling: the cx53 self-hosted runners have a
deliberately small tool surface.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import re
import subprocess
import sys
import tempfile
from collections.abc import Mapping, Sequence
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, NamedTuple

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
REPOS_FILE = REPO_ROOT / "weave-repos.json"
DIGEST_WORKFLOW_FILE = "merge-digest.yml"
DIGEST_DRY_RUN_MARKER = "dry-run"
BOOTSTRAP_WINDOW_HOURS = 24
MAX_SUBSTANCE = 900
MAX_AREAS = 4
DIGEST_CHUNK_BUDGET = 12000
LINEAR_ISSUE_URL = "https://linear.app/krates-ehf/issue/"
TICKET_PATTERN = re.compile(r"\bKRA-\d+\b")
CLOSES_PATTERN = re.compile(r"(?im)^\s*(?:closes|fixes|resolves)\s+(KRA-\d+)")
HTML_COMMENT_PATTERN = re.compile(r"<!--.*?-->", re.DOTALL)
BOILERPLATE_PATTERN = re.compile(
    r"(?im)^\s*(?:closes|fixes|resolves)\s+KRA-\d+\s*$"
    r"|^\s*(?:co-authored-by|generated with|🤖).*$"
    r"|^\s*<?https?://\S*claude\.com/claude-code>?\s*$"
)
SECRET_PATTERNS = (
    re.compile(r"xox[baprs]-[A-Za-z0-9-]{10,}"),
    re.compile(r"gh[pousr]_[A-Za-z0-9]{20,}"),
    re.compile(r"github_pat_[A-Za-z0-9_]{20,}"),
    re.compile(r"AKIA[0-9A-Z]{16}"),
    re.compile(r"sk-[A-Za-z0-9]{20,}"),
    # A PEM is the header, the base64 body, and the matching END marker.
    # Replacing only the BEGIN line leaves a usable key in the Slack post.
    re.compile(
        r"-----BEGIN[A-Z ]*PRIVATE KEY-----"
        r"(?:.*?-----END[A-Z ]*PRIVATE KEY-----|.+)",
        re.DOTALL,
    ),
    # An assignment to anything *named* like a credential. The leading
    # identifier run is what makes `HIVE_BOT_TOKEN=…` match: `\b` does not fire
    # inside an underscored name. Over-redaction is the deliberate direction —
    # a mangled sentence costs a reader a click, a leaked token costs a rotation.
    re.compile(
        r"(?i)[A-Za-z0-9_.\-]*(?:token|secret|password|passwd|api[_-]?key)"
        r"\s*[:=]\s*[\"']?([A-Za-z0-9/+_.\-]{12,})"
    ),
)
REDACTED = "[redacted]"

# Reversal-cost tiers, most expensive first.  The order is the display order:
# the entries whose cheap option is disappearing fastest are the ones where
# reading sooner changes anything.  "unmeasured" ranks above the known-cheap
# tiers: its true cost may be deployed or conflicting, and an unmeasured cost
# reported below "clean" is exactly the cheap claim this file promises never
# to make.
TIER_ORDER = ("deployed", "conflicting", "unmeasured", "dependents", "clean")


def _load_review_loop() -> Any:
    """Load the sibling review-loop helper, reusing an already-loaded copy.

    The digest reports gate outcomes; it must read them through the same code
    that published them.
    """
    existing = sys.modules.get("weave_review_loop")
    if existing is not None:
        return existing
    path = Path(__file__).resolve().parent / "review_loop.py"
    spec = importlib.util.spec_from_file_location("weave_review_loop", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load review-loop helper from {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


review_loop = _load_review_loop()

ApiHttpError = review_loop.ApiHttpError
GitHubApi = review_loop.GitHubApi
SlackApi = review_loop.SlackApi
required_env = review_loop.required_env


def env_flag(name: str) -> bool:
    return os.environ.get(name, "").strip().lower() == "true"


def redact(text: str) -> str:
    """Strip anything shaped like a credential before it reaches Slack.

    PR bodies are human-authored text on the way to a channel; a pasted token
    must not survive the trip.  Redaction is unconditional and applied at the
    single point every message passes through.
    """
    result = text
    for pattern in SECRET_PATTERNS:
        if pattern.groups:
            result = pattern.sub(
                lambda match: match.group(0).replace(match.group(1), REDACTED),
                result,
            )
        else:
            result = pattern.sub(REDACTED, result)
    return result


def load_repos(path: Path | None = None) -> list[dict[str, str]]:
    """Read the declared repository set; an unreadable list is fatal, not empty.

    Reporting zero repositories and reporting zero merges look identical in a
    channel.  Refusing to run keeps the difference visible.
    """
    source = path or REPOS_FILE
    data = json.loads(source.read_text(encoding="utf-8"))
    repos = data.get("repos") if isinstance(data, Mapping) else None
    if not isinstance(repos, list) or not repos:
        raise RuntimeError(f"{source} declares no repositories")
    resolved: list[dict[str, str]] = []
    for entry in repos:
        slug = str(entry.get("slug", "")).strip() if isinstance(entry, Mapping) else ""
        if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", slug):
            raise RuntimeError(
                f"{source} contains an invalid repository slug: {slug!r}"
            )
        role = str(entry.get("role", "")).strip() if isinstance(entry, Mapping) else ""
        resolved.append({"slug": slug, "role": role})
    return resolved


def parse_time(value: Any) -> datetime | None:
    """Parse a GitHub timestamp into an aware UTC datetime, or ``None``.

    Every timestamp in this file is compared against a window bound, and a naive
    datetime raises rather than compares — so the aware-ness is forced here, at
    the one place timestamps enter.
    """
    if not isinstance(value, str) or not value.strip():
        return None
    try:
        parsed = review_loop.parse_github_time(value.strip())
    except ValueError:
        return None
    return parsed.replace(tzinfo=timezone.utc) if parsed.tzinfo is None else parsed


def stamp(moment: datetime) -> str:
    return moment.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%MZ")


def window_start(
    github: GitHubApi,
    *,
    now: datetime,
    current_run_id: str,
    workflow_file: str = DIGEST_WORKFLOW_FILE,
) -> tuple[datetime, str]:
    """Start the window at the previous successful digest run.

    The routine's own run record is the watermark: no state file, no committed
    marker, no second store to drift.  A run that failed never advances it, so a
    failure widens the next window instead of dropping the merges it missed.
    A successful dry run is not a watermark either — it posted nothing, and
    treating it as coverage would permanently skip the merges it only rendered.
    The list is newest-first and paginated until a posting run is found: a
    page of later dry runs is not "no watermark".  Overlap is the safe
    direction and is disclosed in the header — a merge reported twice is
    noise, a merge reported never is the failure this whole ticket exists
    to prevent.
    """
    page = 1
    per_page = 100
    try:
        while True:
            runs = github.request(
                "GET",
                f"repos/{github.repository}/actions/workflows/{workflow_file}/runs",
                query={"status": "success", "per_page": per_page, "page": page},
            )
            entries = runs.get("workflow_runs") if isinstance(runs, Mapping) else None
            if not isinstance(entries, list) or not entries:
                break
            for run in entries:
                if not isinstance(run, Mapping):
                    continue
                if str(run.get("id")) == str(current_run_id):
                    continue
                if not _run_posted_digest(run):
                    continue
                started = parse_time(run.get("created_at"))
                if started is not None:
                    # Newest-first: the first posting run is the watermark.
                    # Stopping at page one would treat a page of later dry
                    # runs as "no watermark" and permanently skip merges
                    # between the real posted run and the 24h bootstrap.
                    return started, "since the previous successful digest run"
            if len(entries) < per_page:
                break
            page += 1
    except ApiHttpError as error:
        if error.status_code != 404:
            raise
    bootstrap = (
        f"first run — bootstrap window of {BOOTSTRAP_WINDOW_HOURS}h, "
        "merges older than that are not covered"
    )
    return now - timedelta(hours=BOOTSTRAP_WINDOW_HOURS), bootstrap


def resolve_window(
    github: GitHubApi,
    *,
    now: datetime,
    current_run_id: str,
    since_override: datetime | None,
) -> tuple[datetime, str]:
    """Apply an optional ``--since`` only when it widens the watermark window.

    A later override would render a narrower digest, then become the next
    ``window_start()`` watermark and permanently drop the merges between the
    old watermark and the override.  Overlap is the safe direction.
    """
    watermark, watermark_source = window_start(
        github, now=now, current_run_id=current_run_id
    )
    if since_override is None:
        return watermark, watermark_source
    if since_override > watermark:
        return (
            watermark,
            (
                "explicit --since is later than the previous posted digest; "
                "using the watermark so the override cannot drop coverage"
            ),
        )
    return since_override, "explicit --since override"


def _run_posted_digest(run: Mapping[str, Any]) -> bool:
    """True when this successful run actually posted, not merely rendered.

    ``merge-digest.yml`` tags dry runs in ``run-name`` so they appear in
    ``display_title``.  The list endpoint does not carry dispatch inputs, so
    the title is the discriminator the watermark can see.
    """
    title = str(run.get("display_title") or "")
    return DIGEST_DRY_RUN_MARKER not in title.lower()


def merged_pulls_since(github: GitHubApi, since: datetime) -> list[Mapping[str, Any]]:
    """Every pull merged into this repository at or after ``since``.

    Listing closed pulls by descending update time and stopping at the first
    page older than the window is exact here: merging always updates the pull,
    so a merge inside the window cannot sit behind the cutoff.
    """
    merged: list[Mapping[str, Any]] = []
    page = 1
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
        if not isinstance(batch, list):
            raise TypeError("GET pulls did not return a list")
        for pull in batch:
            if not isinstance(pull, Mapping):
                continue
            merged_at = parse_time(pull.get("merged_at"))
            if merged_at is not None and merged_at >= since:
                merged.append(pull)
        if not batch or len(batch) < 100:
            return merged
        oldest = parse_time(batch[-1].get("updated_at"))
        if oldest is not None and oldest < since:
            return merged
        page += 1


def substance(body: str) -> str:
    """The account of what changed, taken from the pull body."""
    text = HTML_COMMENT_PATTERN.sub("", body or "")
    lines: list[str] = []
    for raw in text.splitlines():
        line = raw.rstrip()
        if BOILERPLATE_PATTERN.match(line):
            continue
        heading = re.match(r"^\s*#{1,6}\s+(.*)$", line)
        if heading:
            lines.append(f"*{heading.group(1).strip()}*")
            continue
        lines.append(line)
    prose = "\n".join(lines).strip()
    prose = re.sub(r"\n{3,}", "\n\n", prose)
    if len(prose) > MAX_SUBSTANCE:
        cut = prose.rfind("\n", 0, MAX_SUBSTANCE)
        if cut < MAX_SUBSTANCE // 2:
            cut = MAX_SUBSTANCE
        prose = f"{prose[:cut].rstrip()}\n…(body continues)"
    return prose


def ticket_refs(body: str, title: str) -> list[str]:
    """Resolving tickets first, then any other ticket the body names."""
    closes = CLOSES_PATTERN.findall(body or "")
    mentioned = TICKET_PATTERN.findall(f"{title}\n{body or ''}")
    ordered: list[str] = []
    for key in [*closes, *mentioned]:
        if key not in ordered:
            ordered.append(key)
    return ordered


def change_shape(files: Sequence[Mapping[str, Any]]) -> str:
    """Where the change landed and how big it was, rolled up by area."""
    if not files:
        return "no files reported"
    areas: dict[str, list[int]] = {}
    for item in files:
        name = str(item.get("filename") or "")
        parts = name.split("/")
        area = "/".join(parts[:2]) if len(parts) > 2 else (parts[0] if parts else "?")
        bucket = areas.setdefault(area, [0, 0, 0])
        bucket[0] += int(item.get("additions") or 0)
        bucket[1] += int(item.get("deletions") or 0)
        bucket[2] += 1
    ranked = sorted(areas.items(), key=lambda pair: -(pair[1][0] + pair[1][1]))
    shown = ", ".join(
        f"`{area}` +{added}/-{removed}"
        for area, (added, removed, _) in ranked[:MAX_AREAS]
    )
    if len(ranked) > MAX_AREAS:
        shown = f"{shown}, +{len(ranked) - MAX_AREAS} more areas"
    return f"{shown} ({len(files)} files)"


def check_report(github: GitHubApi, sha: str) -> dict[str, Any]:
    """Conclusions of every check run recorded at one commit.

    The checks list endpoint pages at 100. A later-page failure or
    cancellation is still a conclusion of this merge commit; reading only
    page one can report an all-green summary that the remaining runs refute.
    """
    counts = {"success": 0, "failure": 0, "cancelled": 0, "other": 0}
    failed: list[str] = []
    page = 1
    per_page = 100
    seen = 0
    while True:
        payload = github.get(
            f"commits/{sha}/check-runs", query={"per_page": per_page, "page": page}
        )
        runs = payload.get("check_runs") if isinstance(payload, Mapping) else None
        if not isinstance(runs, list) or not runs:
            break
        for run in runs:
            if not isinstance(run, Mapping):
                continue
            conclusion = str(run.get("conclusion") or run.get("status") or "other")
            if conclusion in {"success", "neutral", "skipped"}:
                counts["success" if conclusion == "success" else "other"] += 1
            elif conclusion in {"failure", "timed_out", "action_required"}:
                counts["failure"] += 1
                failed.append(str(run.get("name") or "?"))
            elif conclusion == "cancelled":
                counts["cancelled"] += 1
            else:
                counts["other"] += 1
        seen += len(runs)
        total = payload.get("total_count") if isinstance(payload, Mapping) else None
        if isinstance(total, int) and seen >= total:
            break
        if len(runs) < per_page:
            break
        page += 1
    counts["total"] = sum(
        counts[key] for key in ("success", "failure", "cancelled", "other")
    )
    return {"counts": counts, "failed": failed}


def check_line(report: Mapping[str, Any]) -> str:
    counts = report["counts"]
    if not counts["total"]:
        return "no check run is recorded at this merge commit"
    parts = [f"{counts['success']} green"]
    if counts["failure"]:
        parts.append(
            f"*{counts['failure']} failed* ({', '.join(report['failed'][:3])})"
        )
    if counts["cancelled"]:
        parts.append(f"{counts['cancelled']} cancelled (superseded by a later head)")
    if counts["other"]:
        parts.append(f"{counts['other']} other")
    return ", ".join(parts)


def gate_report(
    github: GitHubApi, pull: Mapping[str, Any], codex_login: str
) -> dict[str, Any]:
    """Report — never re-derive — what the review loop already established.

    Every verdict, round number and finding count here comes out of
    ``review_loop``.  A merged head with no exact-head verdict is stated as
    exactly that: an absence establishes nothing, and hiding it would make the
    digest complicit in the gap.
    """
    number = int(pull["number"])
    merged_head = str((pull.get("head") or {}).get("sha") or "").lower()
    # Pre-merge evidence only: a later verdict cannot rewrite the gate record.
    # Reviews go through ``reviews_as_of_closure`` (REST has no ``updated_at``;
    # GraphQL ``lastEditedAt`` fills it). Issue and inline comments go through
    # ``at_closure`` directly. Both readers share those helpers, so the digest
    # and the belt cannot report different histories for one PR.
    merged_at = str(pull.get("merged_at") or "")
    reviews = review_loop.reviews_as_of_closure(github, number, merged_at)
    review_comments = review_loop.at_closure(
        github.paginate(f"pulls/{number}/comments"), merged_at, "created_at"
    )
    issue_comments = review_loop.at_closure(
        github.paginate(f"issues/{number}/comments"), merged_at, "created_at"
    )
    events = review_loop.codex_result_events(
        github,
        reviews,
        issue_comments,
        codex_login,
        pr_number=number,
        # Already cut at closure above: a review's inline findings are selected
        # by their review's id, so filtering the reviews excludes a post-merge
        # review's comments too, and re-paginating here would not.
        review_comments=review_comments,
    )
    heads = review_loop.result_heads_from_events(events)
    history = review_loop.round_history(
        heads,
        reviews,
        review_comments,
        codex_login,
        latest_results=review_loop.latest_result_by_head(events),
    )
    closing = next((row for row in history if row["head"] == merged_head), None)
    burned = sum(
        row["counts"]["total"] for row in history if row["head"] != merged_head
    )
    # Same predicate as ``pr_belt_summary``: any trusted marker the helper
    # still recognises (legacy form, or a versioned marker under an earlier
    # round bound). Regenerating today's writer form here is a second reader.
    exhausted = review_loop.exhaustion_gate_recorded(issue_comments)
    return {
        "merged_head": merged_head,
        "rounds": len(history),
        "closing": closing,
        "findings_burned": burned,
        "exhaustion_gate": exhausted,
    }


def gate_line(report: Mapping[str, Any]) -> str:
    closing = report["closing"]
    head = report["merged_head"][:8] or "?"
    if closing is None:
        verdict = (
            f"*no Codex verdict resolves to the merged head* `{head}` "
            f"({report['rounds']} reviewed head(s) on this PR)"
        )
    else:
        verdict = (
            f"{closing['verdict']} at `{head}` "
            f"(round {closing['round']}/{closing['rounds']})"
        )
    parts = [verdict]
    if report["findings_burned"]:
        parts.append(f"{report['findings_burned']} findings burned on earlier heads")
    if report["exhaustion_gate"]:
        parts.append("reached the exhaustion gate")
    return " · ".join(parts)


class MergeSpan(NamedTuple):
    """The commits a merged pull actually placed on the default branch.

    GitHub reports one ``merge_commit_sha`` for all three merge strategies and
    publishes the strategy nowhere.  For a squash that sha is the whole change;
    for a merge commit it is the whole change under ``-m 1``; for a **rebase**
    merge it is only the *last* of the pull's replayed commits.  Measuring or
    anchoring on that sha alone therefore reports a partial reversal as a
    complete one — the one claim this file promises never to make.  The span
    carries the commit count so the probe and the anchor both speak about
    everything the merge landed.

    ``undetermined`` is the refusal: a non-empty reason means the span could not
    be derived, and no cost may be claimed from it.
    """

    sha: str
    count: int
    is_merge: bool
    undetermined: str = ""

    def target(self) -> str:
        """The revert argument covering the whole merge, short-sha rendered."""
        short = self.sha[:12]
        return f"{short}~{self.count}..{short}" if self.count > 1 else short

    def diff_spec(self) -> list[str]:
        """``git diff`` arguments spanning every commit the merge landed."""
        if self.is_merge:
            return [f"{self.sha}^1", self.sha]
        if self.count > 1:
            return [f"{self.sha}~{self.count}", self.sha]
        return [f"{self.sha}^!"]

    def revert_args(self) -> list[str]:
        """``git revert`` arguments spanning every commit the merge landed."""
        if self.is_merge:
            return ["-m", "1", self.sha]
        if self.count > 1:
            return [f"{self.sha}~{self.count}..{self.sha}"]
        return [self.sha]


def revert_anchor(span: MergeSpan) -> str:
    """The exact revert command covering everything this merge landed.

    ``-m 1`` belongs on a merge commit and breaks on a squash commit, and a
    rebase merge needs the whole replayed range rather than its tip — all three
    come off the span rather than an assumption about how the repository merges.
    An underivable span says so in the anchor instead of rendering a command
    that may cover only part of the merge.
    """
    if not span.sha:
        return "git revert <merge commit unknown>"
    if span.undetermined:
        return (
            f"git revert {span.sha[:12]} (span undetermined — {span.undetermined}; "
            "confirm by hand whether this sha carries the whole merge)"
        )
    mainline = "-m 1 " if span.is_merge else ""
    return f"git revert {mainline}{span.target()}"


def _commit_identity(commit: Mapping[str, Any]) -> tuple[str, str, str]:
    """Subject, author email and author date — what a rebase preserves.

    A rebase replays a commit under a new sha and a new committer but keeps the
    message and the authorship untouched, so this triple is the same on both
    sides of the replay.  A squash commit shares none of it: GitHub authors it
    as the merger, at merge time, under the pull's title.

    Measured against GitHub itself rather than assumed, 2026-09-05, on a scratch
    repository (``RationallyPrime/kra1372-rebase-probe``, private).  A three-commit
    pull merged with ``gh pr merge --rebase`` produced ``merge_commit_sha`` with one
    parent, subject ``commit number 3``, author ``gnomon@sokrates.is`` at the
    *original* ``2020-01-03T00:00:00Z`` — only the committer was rewritten to the
    merger — and its first-parent chain reproduced all three of the pull's commits
    on this triple, in order.  A two-commit pull merged with ``--squash`` differed
    on all three at once: subject ``squash probe: two commits (#2)``, author the
    merger, date the merge instant.  Both directions therefore rest on a receipt,
    which matters because the author *date* is the leg a rebase could plausibly
    have rewritten and did not.
    """
    payload = commit.get("commit")
    payload = payload if isinstance(payload, Mapping) else {}
    author = payload.get("author")
    author = author if isinstance(author, Mapping) else {}
    lines = str(payload.get("message") or "").splitlines()
    return (
        lines[0].strip() if lines else "",
        str(author.get("email") or "").strip().lower(),
        str(author.get("date") or "").strip(),
    )


def _first_parent_sha(commit: Mapping[str, Any]) -> str:
    parents = commit.get("parents")
    if not isinstance(parents, list) or not parents:
        return ""
    first = parents[0]
    return str(first.get("sha") or "") if isinstance(first, Mapping) else ""


def merge_span(github: GitHubApi, pull: Mapping[str, Any]) -> MergeSpan:
    """How many commits this pull put on the default branch, and under which shape.

    The strategy is read off the history rather than assumed: a rebase merge is
    exactly the case where the merge commit and its first-parent chain reproduce
    the pull's own commits, authorship for authorship.  How many commits there
    are to reproduce comes from the pull's own ``commits`` count rather than
    from the length of the listing, because the listing is capped and the count
    is not — a short list is then a *detected* truncation instead of a silently
    shorter span.  Anything that cannot be read is refused by name — never
    folded into "one commit", which is the silent under-count this function
    exists to prevent.
    """
    merge_sha = str(pull.get("merge_commit_sha") or "").lower()
    if not merge_sha:
        return MergeSpan("", 1, False, "no merge commit is recorded on this pull")
    try:
        merge_commit = github.get(f"commits/{merge_sha}")
    except ApiHttpError:
        return MergeSpan(merge_sha, 1, False, "the merge commit could not be read")
    if not isinstance(merge_commit, Mapping):
        return MergeSpan(merge_sha, 1, False, "the merge commit could not be read")
    parents = merge_commit.get("parents")
    if isinstance(parents, list) and len(parents) > 1:
        # A merge commit holds the pull's whole change against its first parent,
        # so ``-m 1`` reverts all of it however many commits the pull carried.
        return MergeSpan(merge_sha, 1, True)
    declared = pull.get("commits")
    if not isinstance(declared, int) or declared < 1:
        # Only ``GET /pulls/{n}`` carries this count; the list endpoint omits it,
        # as does a detail read that failed and fell back to its list row. Without
        # it a truncated commit listing cannot be told from a complete one, which
        # is exactly the under-count this function exists to prevent.
        return MergeSpan(
            merge_sha, 1, False, "the pull does not report how many commits it carried"
        )
    if declared == 1:
        # One commit lands as one commit under every strategy.
        return MergeSpan(merge_sha, 1, False)
    try:
        number = int(pull["number"])
    except (KeyError, TypeError, ValueError):
        return MergeSpan(merge_sha, 1, False, "the pull carries no usable number")
    try:
        listed = github.paginate(f"pulls/{number}/commits")
    except ApiHttpError:
        return MergeSpan(
            merge_sha, 1, False, "the pull's own commit list could not be read"
        )
    commits = [item for item in listed if isinstance(item, Mapping)]
    if len(commits) != declared:
        # ``GET /pulls/{n}/commits`` stops at 250 however many the pull carries,
        # so a short list is a truncated one. Holding it against the pull's own
        # count catches that without hard-coding the cap, and refuses rather than
        # deriving a span from commits it cannot see.
        return MergeSpan(
            merge_sha,
            1,
            False,
            f"the pull reports {declared} commits and the API lists "
            f"{len(commits)}, so a rebased span could not be derived",
        )
    if _commit_identity(merge_commit) != _commit_identity(commits[-1]):
        # Not the replayed twin of the pull's last commit: a squash commit, whose
        # single sha already carries the whole pull.
        return MergeSpan(merge_sha, 1, False)
    walked: Mapping[str, Any] = merge_commit
    for index in range(len(commits) - 2, -1, -1):
        parent_sha = _first_parent_sha(walked)
        if not parent_sha:
            return MergeSpan(
                merge_sha,
                1,
                False,
                f"rebase merge, {len(commits)} commits — the first-parent chain "
                "ends before the pull's first commit",
            )
        try:
            walked = github.get(f"commits/{parent_sha}")
        except ApiHttpError:
            return MergeSpan(
                merge_sha,
                1,
                False,
                f"rebase merge, {len(commits)} commits — the first-parent chain "
                f"could not be read at {parent_sha[:12]}",
            )
        if not isinstance(walked, Mapping) or _commit_identity(
            walked
        ) != _commit_identity(commits[index]):
            return MergeSpan(
                merge_sha,
                1,
                False,
                f"rebase merge, {len(commits)} commits — the first-parent chain "
                f"diverges from the pull's commits at {parent_sha[:12]}",
            )
    return MergeSpan(merge_sha, len(commits), False)


class GitStepFailed(RuntimeError):
    """A git step that never produced an exit status at all.

    Every reader of ``_git`` branches on a return code, which is what git
    answers with when it runs and fails.  A step that times out or cannot be
    started answers with an exception instead, and that exception used to
    leave ``run_digest`` entirely: one slow clone suppressed the digest for
    every other repository, and since a failed run never becomes the
    watermark, the next run re-probed the same repository and blocked the
    same way.

    Converting at the single point that runs git closes the class rather than
    the instance — a git call added later cannot re-open it.  This is a
    ``RuntimeError``, so the per-repository boundary in ``run_digest``
    contains it by construction and reports that repository UNREAD.  The
    repository, not the pull, is the unit: a timeout is a statement about the
    runner or the network, and continuing would pay the same timeout again
    for every remaining merge in that repository.

    The message is composed rather than inherited from the underlying
    exception: ``TimeoutExpired`` stringifies its whole argv, and this text is
    rendered into the digest.
    """

    def __init__(self, step: str, reason: str, subject: str = "") -> None:
        self.step = step
        self.reason = reason
        self.subject = subject
        tail = f" while probing {subject}" if subject else ""
        super().__init__(f"git {step} {reason}{tail}")


class RevertProbe:
    """Measure reversal cost by attempting the revert, not by proxy.

    "Accurate when checked" is the acceptance criterion, so the check is the
    measurement: clone once per repository, try ``git revert --no-commit`` on
    the live default branch, and count the commits that have since touched the
    same files.  A proxy that says "clean" where the revert conflicts is worse
    than saying nothing, because it is the one claim a reader would act on.

    The credential is passed through the environment into a credential helper.
    It never enters a URL, an argv, or an error message.
    """

    def __init__(self, workdir: Path, token_env: str = "WEAVE_DIGEST_TOKEN") -> None:
        self.workdir = workdir
        self.token_env = token_env
        self.clones: dict[str, Path | None] = {}

    def _git(
        self, args: Sequence[str], cwd: Path | None = None
    ) -> subprocess.CompletedProcess[str]:
        helper = (
            f'!f() {{ echo "username=x-access-token"; '
            f'echo "password=${self.token_env}"; }}; f'
        )
        command = [
            "git",
            "-c",
            "credential.helper=",
            "-c",
            f"credential.helper={helper}",
            "-c",
            "user.name=weave-merge-digest",
            "-c",
            "user.email=digest@sokrates.is",
            *args,
        ]
        step = str(args[0]) if args else "(no subcommand)"
        try:
            return subprocess.run(
                command,
                cwd=str(cwd) if cwd else None,
                capture_output=True,
                text=True,
                timeout=600,
                check=False,
            )
        except subprocess.TimeoutExpired as error:
            raise GitStepFailed(step, f"exceeded {error.timeout:.0f}s") from error
        except (subprocess.SubprocessError, OSError) as error:
            # The whole family, not today's member: a later call passing
            # ``check=True`` raises ``CalledProcessError``, and a runner
            # without git raises ``OSError``.  Both are the same defect —
            # a git step with no exit status to read.
            raise GitStepFailed(
                step, f"could not be run ({type(error).__name__})"
            ) from error

    def clone(self, slug: str) -> Path | None:
        if slug in self.clones:
            return self.clones[slug]
        target = self.workdir / slug.replace("/", "__")
        result = self._git(
            [
                "clone",
                "--filter=blob:none",
                "--no-tags",
                f"https://github.com/{slug}.git",
                str(target),
            ]
        )
        self.clones[slug] = target if result.returncode == 0 else None
        return self.clones[slug]

    def cost(self, slug: str, span: MergeSpan, default_branch: str) -> dict[str, Any]:
        """Measure the revert, naming what the measurement was about if it dies.

        The failure a caller sees carries the step and the merge it was
        probing; ``run_digest`` prefixes the repository, so the digest line
        names all three.
        """
        if span.undetermined:
            # An underivable span is not a one-commit span. Measuring the tip
            # alone would price a partial reversal as the whole merge.
            return {
                "tier": "unmeasured",
                "dependents": 0,
                "detail": (
                    f"`{revert_anchor(span)}` — the commits this merge landed "
                    "could not be derived, so no reversal cost is claimed"
                ),
            }
        try:
            return self._measure(slug, span, default_branch)
        except GitStepFailed as error:
            raise GitStepFailed(
                error.step, error.reason, f"the revert of `{span.sha[:12]}`"
            ) from error

    def _measure(
        self, slug: str, span: MergeSpan, default_branch: str
    ) -> dict[str, Any]:
        anchor = revert_anchor(span)
        merge_sha = span.sha
        repo = self.clone(slug)
        if repo is None:
            return {
                "tier": "unmeasured",
                "dependents": 0,
                "detail": "repository could not be cloned on this runner",
            }
        fetched = self._git(
            ["fetch", "--filter=blob:none", "origin", merge_sha], cwd=repo
        )
        if fetched.returncode != 0:
            return {
                "tier": "unmeasured",
                "dependents": 0,
                "detail": "merge commit is not reachable from this clone",
            }
        checkout = self._git(
            ["checkout", "--force", "--detach", f"origin/{default_branch}"], cwd=repo
        )
        if checkout.returncode != 0:
            return {
                "tier": "unmeasured",
                "dependents": 0,
                "detail": f"default branch `{default_branch}` could not be checked out",
            }
        self._git(["reset", "--hard"], cwd=repo)
        self._git(["clean", "-ffdq"], cwd=repo)
        attempt = self._git(["revert", "--no-commit", *span.revert_args()], cwd=repo)
        clean = attempt.returncode == 0
        # A revert of an already-reverted merge "succeeds" while staging nothing;
        # reporting that as an applicable revert promises work that would fail
        # with nothing-to-commit.
        noop = (
            clean and not self._git(["status", "--porcelain"], cwd=repo).stdout.strip()
        )
        self._git(["revert", "--quit"], cwd=repo)
        self._git(["reset", "--hard"], cwd=repo)
        self._git(["clean", "-ffdq"], cwd=repo)
        paths = self._changed_paths(repo, span)
        dependents = (
            None
            if paths is None
            else self._dependent_commits(repo, merge_sha, default_branch, paths)
        )
        if dependents is None:
            # A failed probe is not "0 later commits". Folding the failure
            # into zero would report a clean revert the evidence does not
            # carry — the cheap claim this file promises never to make.
            return {
                "tier": "unmeasured",
                "dependents": 0,
                "detail": (f"`{anchor}` — dependent history could not be measured"),
            }
        if noop:
            return {
                "tier": "clean",
                "dependents": dependents,
                "detail": (
                    f"`{anchor}` is a no-op — this merge appears already reverted "
                    f"on `{default_branch}`; nothing is left to revert"
                ),
            }
        if not clean:
            return {
                "tier": "conflicting",
                "dependents": dependents,
                "detail": (
                    f"`{anchor}` no longer applies — the revert conflicts and must "
                    "be untangled by hand"
                ),
            }
        if dependents:
            return {
                "tier": "dependents",
                "dependents": dependents,
                "detail": (
                    f"`{anchor}` still applies, but {dependents} later commit(s) "
                    "touch the same files and would need follow-up repair if "
                    "the revert drops required behavior"
                ),
            }
        return {
            "tier": "clean",
            "dependents": 0,
            "detail": f"clean revert — `{anchor}` applies with no conflict and nothing stacked on it",
        }

    def _changed_paths(self, repo: Path, span: MergeSpan) -> list[str] | None:
        result = self._git(["diff", "--name-only", *span.diff_spec()], cwd=repo)
        if result.returncode != 0:
            return None
        return [line for line in result.stdout.splitlines() if line.strip()]

    def _dependent_commits(
        self, repo: Path, merge_sha: str, default_branch: str, paths: Sequence[str]
    ) -> int | None:
        if not paths:
            return 0
        # Union across path chunks: one truncated invocation would silently drop
        # commits touching only paths past the cutoff and misreport "clean".
        shas: set[str] = set()
        for start in range(0, len(paths), 200):
            result = self._git(
                [
                    "log",
                    "--format=%H",
                    f"{merge_sha}..origin/{default_branch}",
                    "--",
                    *paths[start : start + 200],
                ],
                cwd=repo,
            )
            if result.returncode != 0:
                return None
            shas.update(line for line in result.stdout.splitlines() if line.strip())
        return len(shas)


def deployment_note(
    github: GitHubApi,
    merged_at: datetime | None,
    *,
    merge_sha: str = "",
    default_branch: str = "",
) -> str:
    """Whether state has been shipped behind this merge, or whether that is unknown.

    A repository that publishes no deployment records cannot answer the
    question.  Saying so is the honest half of the tier — reporting "not
    deployed" from an empty list would be a claim the evidence does not carry.
    Only a successful deployment of this revision (the merge commit or the
    default branch it landed on) establishes the shipped tier.  Staging,
    failed, and unrelated-ref records do not.  Newer preview or staging
    records commonly fill the first page, so pagination continues until a
    covering production success is found or remaining records predate the
    merge — stopping at page one would leave shipped code in a cheaper tier.
    """
    page = 1
    saw_records = False
    try:
        while True:
            payload = github.get("deployments", query={"per_page": 100, "page": page})
            if not isinstance(payload, list):
                return "deployment records unreadable"
            if not payload:
                if not saw_records:
                    return (
                        "repo publishes no deployment records — "
                        "deployed state not established"
                    )
                return ""
            saw_records = True
            if merged_at is None:
                return ""
            page_predates_merge = False
            for deployment in payload:
                if not isinstance(deployment, Mapping):
                    continue
                created = parse_time(deployment.get("created_at"))
                if created is None or created < merged_at:
                    if created is not None:
                        page_predates_merge = True
                    continue
                if not _deployment_covers_merge(
                    deployment, merge_sha=merge_sha, default_branch=default_branch
                ):
                    continue
                if not _deployment_is_production(deployment):
                    continue
                succeeded = _deployment_succeeded(github, deployment)
                if succeeded is None:
                    return (
                        "deployment status unreadable for a covering production "
                        "deployment — shipped state unknown"
                    )
                if not succeeded:
                    continue
                environment = str(deployment.get("environment") or "production")
                return (
                    f"deployed since this merge to `{environment}` — "
                    "reverting now means reverting shipped state"
                )
            if page_predates_merge or len(payload) < 100:
                return ""
            page += 1
    except ApiHttpError:
        return "deployment records unreadable"


_NON_PRODUCTION_ENVIRONMENTS = frozenset(
    {"staging", "preview", "dev", "development", "qa", "test"}
)


def _deployment_covers_merge(
    deployment: Mapping[str, Any], *, merge_sha: str, default_branch: str
) -> bool:
    sha = str(deployment.get("sha") or "").lower()
    if merge_sha and sha == merge_sha.lower():
        return True
    ref = str(deployment.get("ref") or "")
    return bool(
        default_branch and ref in {default_branch, f"refs/heads/{default_branch}"}
    )


def _deployment_is_production(deployment: Mapping[str, Any]) -> bool:
    if deployment.get("production_environment") is False:
        return False
    environment = str(deployment.get("environment") or "").lower()
    return environment not in _NON_PRODUCTION_ENVIRONMENTS


def _deployment_succeeded(
    github: GitHubApi, deployment: Mapping[str, Any]
) -> bool | None:
    """True/False from the latest status; ``None`` when the status is unreadable.

    A transient 403/5xx on the status endpoint is not evidence the deployment
    failed — folding it into ``False`` silently drops the shipped tier.
    """
    deployment_id = deployment.get("id")
    if deployment_id is None:
        return False
    try:
        statuses = github.get(
            f"deployments/{deployment_id}/statuses", query={"per_page": 100}
        )
    except ApiHttpError:
        return None
    if not isinstance(statuses, list) or not statuses:
        return False
    latest = statuses[0]
    if not isinstance(latest, Mapping):
        return False
    return str(latest.get("state") or "") == "success"


def build_entry(
    github: GitHubApi,
    *,
    slug: str,
    pull: Mapping[str, Any],
    codex_login: str,
    probe: RevertProbe | None,
    default_branch: str,
) -> dict[str, Any]:
    number = int(pull["number"])
    body = str(pull.get("body") or "")
    title = str(pull.get("title") or "")
    merged_at = parse_time(pull.get("merged_at"))
    span = merge_span(github, pull)
    merge_sha = span.sha
    files = github.paginate(f"pulls/{number}/files")
    account = substance(body)
    gate = gate_report(github, pull, codex_login)
    checks = (
        check_report(github, merge_sha)
        if merge_sha
        else {"counts": {"total": 0}, "failed": []}
    )
    if probe is not None and merge_sha:
        reversal = probe.cost(slug, span, default_branch)
        shipped = deployment_note(
            github,
            merged_at,
            merge_sha=merge_sha,
            default_branch=default_branch,
        )
        if shipped.startswith("deployed since"):
            reversal = {
                **reversal,
                "tier": "deployed",
                "detail": f"{reversal['detail']}; {shipped}",
            }
        elif shipped:
            reversal = {**reversal, "detail": f"{reversal['detail']} ({shipped})"}
    else:
        reversal = {
            "tier": "unmeasured",
            "dependents": 0,
            "detail": (
                f"`{revert_anchor(span)}` — the anchor only. "
                "Nothing has been measured at merge time, and an unmeasured "
                "cost is never reported as a cheap one; the scheduled digest "
                "measures it."
            ),
        }
    merged_by = (pull.get("merged_by") or {}).get("login") or "?"
    return {
        "slug": slug,
        "number": number,
        "title": title,
        "url": str(pull.get("html_url") or ""),
        "merge_sha": merge_sha,
        "merged_at": merged_at,
        "merged_by": str(merged_by),
        "seat": "",
        "account": account,
        "shape": change_shape(files),
        "tickets": ticket_refs(body, title),
        "gate": gate,
        "checks": checks,
        "reversal": reversal,
    }


def ticket_links(keys: Sequence[str]) -> str:
    return (
        ", ".join(f"<{LINEAR_ISSUE_URL}{key}|{key}>" for key in keys[:4])
        or "no ticket named"
    )


def urgency_key(entry: Mapping[str, Any]) -> tuple[int, int, float]:
    tier = entry["reversal"]["tier"]
    rank = TIER_ORDER.index(tier) if tier in TIER_ORDER else len(TIER_ORDER)
    merged_at = entry.get("merged_at")
    return (
        rank,
        -int(entry["reversal"].get("dependents") or 0),
        merged_at.timestamp() if merged_at else 0.0,
    )


def render_entry(entry: Mapping[str, Any], index: int) -> str:
    lines = [
        f"*{index}. <{entry['url']}|{entry['slug']}#{entry['number']}>* — {entry['title']}",
        entry["account"] if entry["account"] else "_(empty body)_",
    ]
    lines.append(f"• *Ticket:* {ticket_links(entry['tickets'])}")
    lines.append(f"• *Shape:* {entry['shape']}")
    lines.append(f"• *Gated by:* {gate_line(entry['gate'])}")
    lines.append(f"• *Checks at the merge commit:* {check_line(entry['checks'])}")
    merged = stamp(entry["merged_at"]) if entry["merged_at"] else "?"
    seat = f", authored by {entry['seat']}" if entry["seat"] else ""
    lines.append(f"• *Merged:* {merged} by `{entry['merged_by']}`{seat}")
    lines.append(f"• *Reversing it now:* {entry['reversal']['detail']}")
    lines.append(f"• *Veto:* reply `VETO {entry['slug']}#{entry['number']} — <reason>`")
    return "\n".join(lines) + "\n"


def digest_header(
    *,
    since: datetime,
    until: datetime,
    window_source: str,
    entry_count: int,
    repo_status: Sequence[str],
) -> str:
    coverage = " · ".join(repo_status)
    if entry_count:
        opening = f"{entry_count} machine merge(s) landed in this window."
    else:
        opening = (
            "*No machine merges in this window.* Nothing landed without Hákon "
            "authoring it — this is a reported result, not a missing report."
        )
    return (
        "*Machine-merge digest*\n"
        f"Window: {stamp(since)} → {stamp(until)} ({window_source}). "
        "Windows overlap rather than gap: a failed run widens the next one.\n"
        f"{opening}\n"
        f"Repos read: {coverage}\n"
        "The merge-ready boundary is unchanged — this reports desirability, not "
        "correctness, and re-verifies nothing.\n"
        "*Your veto never expires.* Ordered by what exercising it costs today, "
        "most expensive first; a veto is an instruction to a seat, and the "
        "reversal travels the ordinary reviewed path.\n\n"
    )


def chunk(
    header: str, blocks: Sequence[str], *, budget: int = DIGEST_CHUNK_BUDGET
) -> list[str]:
    return review_loop.chunk_digest(
        header, blocks, label="machine-merge digest", budget=budget
    )


def emit(messages: Sequence[str], *, dry_run: bool) -> None:
    safe = [redact(message) for message in messages]
    if dry_run:
        for message in safe:
            print(message)
            print("---")
        return
    slack = SlackApi(required_env("HIVE_BOT_TOKEN"), required_env("HIVE_CHANNEL"))
    # Not ``post_threaded_messages``: that boundary re-decides liveness against
    # one pull request immediately before the addressed message, and this digest
    # has none — it reports a window of merges across every repository read, all
    # of them already merged by definition.  KRA-1226 made those five arguments
    # required, which is right for every wake and impossible here.
    review_loop.post_threaded_digest_without_a_pull_subject(
        slack, safe, subject="machine-merge digest"
    )


def seat_for_pull(github: GitHubApi, pull: Mapping[str, Any]) -> tuple[str, str] | None:
    """The authoring seat, resolved exactly as the review loop resolves it.

    Merge actor is not the discriminator: a seat and a human both merge with a
    credential that authenticates as Hákon.  Authorship is what separates work
    the machines produced from work he wrote himself, and it is already the
    review loop's seat identity — so it stays one implementation.
    """
    head_sha = str((pull.get("head") or {}).get("sha") or "")
    return review_loop.author_for_pr(github, int(pull["number"]), head_sha, pull)


def run_digest(*, dry_run: bool = False, since_override: str | None = None) -> None:
    token = required_env("WEAVE_DIGEST_TOKEN")
    codex_login = os.environ.get("CODEX_LOGIN", review_loop.CODEX_LOGIN)
    now = datetime.now(timezone.utc)
    self_repo = os.environ.get("GITHUB_REPOSITORY", "Skrates/weave-doctrine")
    run_id = os.environ.get("GITHUB_RUN_ID", "")
    parsed_override: datetime | None = None
    if since_override:
        parsed_override = parse_time(since_override)
        if parsed_override is None:
            raise RuntimeError(
                f"--since is not an ISO-8601 UTC timestamp: {since_override!r}"
            )
    since, window_source = resolve_window(
        GitHubApi(token, self_repo),
        now=now,
        current_run_id=run_id,
        since_override=parsed_override,
    )
    entries: list[dict[str, Any]] = []
    repo_status: list[str] = []
    failures: list[str] = []
    with tempfile.TemporaryDirectory(prefix="weave-merge-digest-") as tmp:
        probe = RevertProbe(Path(tmp))
        for repo in load_repos():
            slug = repo["slug"]
            github = GitHubApi(token, slug)
            try:
                meta = github.request("GET", f"repos/{slug}")
                if not isinstance(meta, Mapping):
                    raise TypeError("repository lookup did not return an object")
                default_branch = str(meta.get("default_branch") or "main")
                pulls = merged_pulls_since(github, since)
                counted = 0
                repo_entries: list[dict[str, Any]] = []
                for pull in pulls:
                    seat = seat_for_pull(github, pull)
                    if seat is None:
                        continue
                    # Who pressed merge is only on the detail endpoint, never on
                    # the list one — and it is read after the seat filter so the
                    # extra call is paid once per machine merge, not per closed PR.
                    detail = github.get(f"pulls/{int(pull['number'])}")
                    resolved = detail if isinstance(detail, Mapping) else pull
                    # Probe the branch the merge actually landed on: reverting a
                    # release-branch merge against the default branch measures an
                    # unrelated tree.
                    base_ref = str(
                        (resolved.get("base") or {}).get("ref") or default_branch
                    )
                    entry = build_entry(
                        github,
                        slug=slug,
                        pull=resolved,
                        codex_login=codex_login,
                        probe=probe,
                        default_branch=base_ref,
                    )
                    entry["seat"] = seat[0]
                    repo_entries.append(entry)
                    counted += 1
                entries.extend(repo_entries)
                repo_status.append(f"`{slug}` {counted}")
            except (ApiHttpError, RuntimeError, TypeError) as error:
                repo_status.append(f"`{slug}` *UNREAD*")
                failures.append(f"`{slug}`: {error}")
                continue
        entries.sort(key=urgency_key)
        blocks = [
            render_entry(entry, index) for index, entry in enumerate(entries, start=1)
        ]
        header = digest_header(
            since=since,
            until=now,
            window_source=window_source,
            entry_count=len(entries),
            repo_status=repo_status,
        )
        messages = chunk(header, blocks)
        if failures:
            messages.append(
                "*Machine-merge digest — repositories that could not be read.* "
                "These are not zero-merge repos; they are unknown, and the "
                "digest above is incomplete by exactly this much:\n"
                + "\n".join(f"• {failure}" for failure in failures)
            )
        emit(messages, dry_run=dry_run)
    print(
        f"machine-merge digest: {len(entries)} entries, {len(failures)} unreadable repos"
    )
    if failures:
        raise RuntimeError(
            "digest incomplete: "
            + "; ".join(failures)
            + " — this run must not become the watermark"
        )


def announce_message(entry: Mapping[str, Any]) -> str:
    """One substance line at merge time — what it does, plus the revert anchor."""
    headline = (
        f"*Machine merge* — <{entry['url']}|{entry['slug']}#{entry['number']}> "
        f"{entry['title']}"
    )
    lines = [headline, entry["account"] if entry["account"] else "_(empty body)_"]
    lines.append(f"• *Ticket:* {ticket_links(entry['tickets'])}")
    lines.append(f"• *Gated by:* {gate_line(entry['gate'])}")
    lines.append(f"• *Checks at the merge commit:* {check_line(entry['checks'])}")
    merged = stamp(entry["merged_at"]) if entry["merged_at"] else "?"
    lines.append(
        f"• *Merged:* {merged} by `{entry['merged_by']}`, authored by {entry['seat']}"
    )
    lines.append(f"• *Revert anchor:* {entry['reversal']['detail']}")
    lines.append(
        f"• *Veto:* reply `VETO {entry['slug']}#{entry['number']} — <reason>`. "
        "The veto never expires; only its price rises."
    )
    return "\n".join(lines)


def run_announce(*, dry_run: bool = False) -> None:
    token = required_env("GITHUB_TOKEN")
    slug = required_env("GITHUB_REPOSITORY")
    codex_login = os.environ.get("CODEX_LOGIN", review_loop.CODEX_LOGIN)
    event = review_loop.load_event()
    pull = event.get("pull_request")
    if not isinstance(pull, Mapping):
        raise TypeError("announce requires a pull_request event payload")
    if not pull.get("merged"):
        print(
            f"{slug}#{pull.get('number')} closed without merging; nothing to announce"
        )
        return
    github = GitHubApi(token, slug)
    live = github.get(f"pulls/{int(pull['number'])}")
    if not isinstance(live, Mapping):
        raise TypeError("pull request lookup did not return an object")
    seat = seat_for_pull(github, live)
    if seat is None:
        print(
            f"{slug}#{live['number']} is not seat-authored; no machine-merge announcement"
        )
        return
    entry = build_entry(
        github,
        slug=slug,
        pull=live,
        codex_login=codex_login,
        probe=None,
        default_branch=str((live.get("base") or {}).get("ref") or "main"),
    )
    entry["seat"] = seat[0]
    emit([announce_message(entry)], dry_run=dry_run)
    print(f"announced machine merge {slug}#{live['number']}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("announce", "digest"))
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="render to stdout instead of posting to Hive",
    )
    parser.add_argument(
        "--since",
        default=None,
        help=(
            "ISO-8601 UTC window start; only widens the previous-run watermark "
            "(a later value is ignored so the override cannot drop coverage)"
        ),
    )
    args = parser.parse_args(argv)
    # Workflow-dispatch inputs arrive through the environment rather than the
    # command line, so a dispatched value can never become part of a shell
    # command in a step that holds credentials.
    dry_run = args.dry_run or env_flag("DIGEST_DRY_RUN")
    since = args.since or os.environ.get("DIGEST_SINCE", "").strip() or None
    try:
        if args.command == "digest":
            run_digest(dry_run=dry_run, since_override=since)
        else:
            run_announce(dry_run=dry_run)
    except Exception as error:  # noqa: BLE001 - CLI boundary must terminalize visibly.
        print(f"merge-digest {args.command} failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
