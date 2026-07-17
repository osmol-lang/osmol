# Osmol — Phase 2 Report

## Theorem 1 (Convergence): Machine-Checked ✅

**Verifier:** Coq 8.18.0 · **Result:** accepted, first compile · **Assumptions:** `Closed under the global context` (zero axioms, zero `Admitted`) · **Date:** July 17, 2026

---

## What the machine now certifies

Three statements about Osmol meshes are no longer claims. They are theorems, checked symbol by symbol by a proof assistant that cannot be charmed, rushed, or persuaded.

**`convergence`** — The osmosis step relation is well-founded: there exists no infinite sequence of flows. Every finite mesh, left without external input, settles. Equilibrium is not a hope of the design; it is a mathematical necessity of it.

**`chain_bound`** — The quantitative version: a mesh whose twins carry *g* open gaps in total reaches equilibrium in **at most g flows**. Settling isn't just finite — it's bounded by the amount of unmet demand, and by nothing else.

**`zero_is_equilibrium`** — A mesh with no open gaps admits no flow at all. In Osmol's semantics, silence is a fixpoint, not a failure state. A quiet phone is the system working.

## The model, and the honesty block

The proof formalizes the distilled core of Spec §6. A twin is a pair *(holds, gaps)*; a flow requires a holder, a seeker, and a grant; its sole effect is to close one gap and add one holding. Two modeling choices deserve daylight.

First, membrane, trust, urgency, and threshold are folded into a single boolean oracle, and the theorem is proven **for every possible oracle**. This is a strengthening, not a shortcut: convergence cannot depend on anyone's permission policy, pressure formula, or attention budget — the proof holds for all of them at once, including adversarial ones.

Second, the theorem's own precondition — "no external input" — is encoded by the step relation being the *only* rule. New declarations, decays, and arriving legacy email perturb a real mesh continuously; what the theorem guarantees is that between perturbations, the solver always finds the floor. It never oscillates, never loops, never runs away.

The load-bearing lemma is exactly the axiom the language was built on: **`step_decreases`** — every flow strictly reduces total open demand. Monotone absorption in, well-foundedness out. The spec's promise and the proof's engine are the same sentence.

## Reproduce it yourself

```
apt-get install coq        # Coq 8.18+
coqc osmol_convergence.v   # exit code 0; prints the assumption audit
```

The file ends with `Print Assumptions` on all three theorems — the verifier itself reports that nothing was assumed. It also contains the maya/raj mesh from Spec §8 as a checked example: one open gap, provably at most one flow to equilibrium.

## What remains on the Phase 2 ledger

Theorem 2 (Non-interference) and Theorem 4 (Granularity monotonicity) are formalizable in this same framework by enriching the oracle back into structure — membranes as explicit casts, facts as (value, granularity) pairs. Theorem 3 (Attention soundness) needs a placement layer on top of flows. Theorem 5 (Spam irrationality) is game-theoretic and wants a different toolbox. None of them block Phase 3.

**Phase status: language ✅ · core proof ✅ · prototype → next.**
