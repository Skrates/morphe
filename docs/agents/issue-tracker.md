# Issue tracker: Linear

Issues and PRDs for this repo live in **Linear**, not GitHub. The GitHub remote
(`Skrates/morphe`) is for code only — **do not** `gh issue create`. Use the
**`linear` MCP tools** for all issue operations.

## Coordinates

- **Workspace:** Krates (`krates-ehf`).
- **Team:** `Krates-ehf` (id `8d2e6309-a042-4899-86e3-10b215c4f93e`). Issue keys are `KRA-###`.
- **Project:** `Morphe` (slug `morphe-f0174d9a64df`) —
  <https://linear.app/krates-ehf/project/morphe-f0174d9a64df>.
  **New Morphe issues belong in this project, on this team.**

## Conventions (linear MCP tools)

- **Create an issue:** `save_issue` with `team: "Krates-ehf"`, `project: "Morphe"`,
  a `title`, a markdown `description`, and `labels` (see `triage-labels.md`). Omit `id`
  to create. Send markdown with real newlines, not `\n` escapes.
- **Read an issue:** `get_issue` with the identifier (e.g. `KRA-274`), then
  `list_comments` with that `issueId` for the discussion + inline (anchored) comments.
- **List issues:** `list_issues` filtered by `team: "Krates-ehf"`, `project: "Morphe"`,
  and `label` / `state` as needed (e.g. `label: "ready-for-agent"` for AFK-ready work).
- **Comment on an issue:** `save_comment` with `issueId` and `body`.
- **Apply / change labels or state:** `save_issue` with the existing `id` and the new
  `labels` / `state`. (Labels replace; fetch current via `get_issue` first if you need
  to add rather than overwrite.) Discover label + status names with `list_issue_labels`
  / `list_issue_statuses` for team `Krates-ehf` — never invent a label string.
- **Close / decline:** set the issue `state` to the team's Done/Canceled status via
  `save_issue`; for "parked, not now" apply the `deferred-post-v1` label (see
  `triage-labels.md`).

## When a skill says "publish to the issue tracker"

Create a Linear issue in the **Morphe** project on team **Krates-ehf** via `save_issue`.

## When a skill says "fetch the relevant ticket"

`get_issue` for the `KRA-###` identifier, then `list_comments` for that issue.

## Design narrative ↔ issues

The home-redesign work is narrated in `docs/redesign-plan.md`; issues `KRA-274..KRA-283`
each link back to it. When breaking a plan into issues, keep that pattern — the doc holds
the rationale, the issue holds the actionable slice.
