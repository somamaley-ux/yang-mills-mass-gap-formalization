# Yang-Mills Editor Note

Date: 2026-04-15

## Purpose

This note is meant for editorial screening.

Its purpose is modest:

- to show that the submission is organized into a referee-manageable core paper
  plus companions,
- to identify the current Lean verification boundary accurately,
- and to reduce uncertainty about proof structure before external review.

## What the Lean repository currently provides

The current Yang--Mills Lean layer provides:

- a theorem-register and claim-ledger representation of the manuscript-facing
  proof burden,
- source-label and witness-label crosswalks back to the manuscript corpus,
- a closed manuscript instantiation,
- and a top native package theorem spanning the constructive, vacuum-gap, and
  endpoint chains.

The current strongest theorem boundary is:

- `MaleyLean.YangMillsFullManuscriptNativePackageExportStatement`

This boundary is summarized in:

- `reports/audits/yang_mills_submission_layer_audit_2026-04-15.md`

## What the Lean repository does not claim

The repository is not being presented as a completed full native Lean
derivation of all analytic Yang--Mills arguments.

The accurate current claim is narrower:

- the manuscript-facing theorem architecture is deeply encoded,
- the main constructive, mass-gap, and endpoint routes are tied together in one
  axiom-free top theorem boundary,
- and the repo provides a checkable dependency and crosswalk layer that should
  make refereeing more efficient.

## Why this lowers editorial risk

For desk review purposes, the Lean repository reduces risk in three ways:

- it makes the proof architecture explicit rather than leaving theorem flow
  implicit in long prose,
- it isolates where the core proof burden lives across the main paper and the
  companions,
- and it gives referees a concrete audit trail for theorem labels, witness
  labels, and route composition.

## Recommended editorial reading order

1. Read the core paper for the main mathematical claim and proof spine.
2. Use the companion map in `reports/submission` to identify where each proof
   burden is developed in detail.
3. Use the Lean verification note only as a structural aid, not as a substitute
   for mathematical review.
