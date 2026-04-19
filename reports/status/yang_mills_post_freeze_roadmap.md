# Yang--Mills Post-Freeze Roadmap

Last updated: 2026-04-19

## Purpose

This note records what should count as a genuine next phase after the
`ym-paper-v1.2.1` freeze marker.

It is not a reopening of the frozen extension stack. It is a boundary note for
future work.

## What is frozen

The current extension-paper package should be treated as closed for now.

That means the following are not the default next steps:

- another broad documentation rewrite
- more status-note tightening without new theorem-level content
- reopening the four critical seams just to restate already-fixed results

## What would justify a new phase

A real next phase should be driven by one of these:

1. A stricter manuscript-faithfulness pass.
   This would tighten the Section 4 theorem-scope wording and any last Section 8
   support-route presentation until the code-facing and manuscript-facing forms
   align even more tightly.

2. A deeper proof-home internalization pass.
   This would move beyond the current manuscript-facing dossier standard toward
   native Lean internalization of more cited analytic proof homes.

3. A new mathematical export pass.
   This would add genuinely new theorem surfaces, witness structures, or
   companion-level claims beyond the current frozen boundary.

4. A submission/referee tooling pass.
   This would improve auditability, support maps, reading order, and reviewer
   ergonomics without pretending that such work is new mathematics.

## Best default recommendation

If work resumes soon, the highest-value next phase is probably:

- a selective manuscript-faithfulness pass on Section 4 and the remaining
  Section 8 support-route wording

If the goal is deeper than manuscript-facing closure, the strongest ambitious
next phase is:

- proof-home internalization aimed at replacing more cited analytic burden with
  native Lean mathematics

## Current boundary discipline

Until one of those next-phase goals is chosen explicitly, the right default is:

- keep the extension stack frozen at `ym-paper-v1.2.1`
- treat the current dossier as the stable reference boundary
- avoid reopening settled seams without a clearly stronger mathematical target
