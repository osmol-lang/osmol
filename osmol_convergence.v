(* ================================================================== *)
(*  OSMOL — Phase 2                                                    *)
(*  Theorem 1 (Convergence), machine-checked.                          *)
(*                                                                     *)
(*  Spec §9, Theorem 1: "Every finite mesh with no external input      *)
(*  reaches equilibrium in finitely many steps."                       *)
(*                                                                     *)
(*  Model notes (honesty block):                                       *)
(*  - Facts are drawn from a countable universe (nat, WLOG).           *)
(*  - A twin is (holds, gaps): assertions possessed, absences sought.  *)
(*  - Membrane, trust, urgency and threshold are folded into a single  *)
(*    boolean oracle `allowed`. Convergence must hold for EVERY        *)
(*    membrane/pressure policy, so we quantify over all oracles        *)
(*    rather than fixing one. This is a strengthening, not a cheat.    *)
(*  - The step relation encodes Axiom "absorption is monotone":        *)
(*    a flow closes exactly one gap at the receiver and adds a         *)
(*    holding; no rule creates a gap. "No external input" = no other   *)
(*    rule exists.                                                     *)
(* ================================================================== *)

Require Import List Arith Lia.
Require Import Coq.Arith.Wf_nat.
Import ListNotations.

(* ---------- The universe of facts ---------- *)

Definition fact : Type := nat.
Definition fact_eq_dec : forall x y : fact, {x = y} + {x <> y} := Nat.eq_dec.

(* ---------- Twins: cognitive state models ---------- *)

Record twin : Type := Twin {
  holds : list fact ;   (* assertions the twin possesses  *)
  gaps  : list fact     (* registered absences (seek ...) *)
}.

(* ---------- The mesh ---------- *)

Record mesh : Type := Mesh {
  twins   : list twin ;
  allowed : nat -> nat -> fact -> bool
  (* allowed a b k  ≡  membrane grants a→b on k  ∧  P(a→b,k) > θ_b *)
}.

(* ---------- The measure: total open demand ---------- *)

Fixpoint total (l : list twin) : nat :=
  match l with
  | []      => 0
  | t :: r  => length (gaps t) + total r
  end.

Definition gapcount (m : mesh) : nat := total (twins m).

(* ---------- List surgery ---------- *)

Fixpoint replace {A : Type} (l : list A) (i : nat) (x : A) : list A :=
  match l, i with
  | [], _          => []
  | _ :: t, 0      => x :: t
  | h :: t, S i'   => h :: replace t i' x
  end.

(* ---------- The osmosis step (Spec §6) ---------- *)
(*  One flow: twin a holds k, twin b seeks k, the oracle grants it.    *)
(*  Effect at b: gap k closes, holding k appears. Nothing else moves.  *)

Inductive step : mesh -> mesh -> Prop :=
| flow : forall (m : mesh) (a b : nat) (A B : twin) (k : fact),
    nth_error (twins m) a = Some A ->
    nth_error (twins m) b = Some B ->
    In k (holds A) ->
    In k (gaps B) ->
    allowed m a b k = true ->
    step m (Mesh (replace (twins m) b
                    (Twin (k :: holds B)
                          (remove fact_eq_dec k (gaps B))))
                 (allowed m)).

(* ================================================================== *)
(*  Lemmas                                                             *)
(* ================================================================== *)

(* Removing a fact never lengthens a list. *)
Lemma remove_le : forall (l : list fact) (x : fact),
  length (remove fact_eq_dec x l) <= length l.
Proof.
  induction l as [| h t IH]; intros x; simpl.
  - lia.
  - destruct (fact_eq_dec x h); simpl.
    + specialize (IH x). lia.
    + specialize (IH x). lia.
Qed.

(* Removing a fact that is present strictly shortens the list.        *)
(* (Absorption really closes something.)                               *)
Lemma remove_lt : forall (l : list fact) (x : fact),
  In x l -> length (remove fact_eq_dec x l) < length l.
Proof.
  induction l as [| h t IH]; intros x Hin; simpl.
  - contradiction.
  - destruct (fact_eq_dec x h) as [e | ne].
    + pose proof (remove_le t x). lia.
    + destruct Hin as [Hh | Ht].
      * congruence.
      * simpl. specialize (IH x Ht). lia.
Qed.

(* Replacing one twin by a twin with strictly fewer gaps strictly     *)
(* lowers the mesh's total demand.                                    *)
Lemma total_replace_lt : forall (l : list twin) (i : nat) (OLD NEW : twin),
  nth_error l i = Some OLD ->
  length (gaps NEW) < length (gaps OLD) ->
  total (replace l i NEW) < total l.
Proof.
  induction l as [| h t IH]; intros i OLD NEW Hnth Hlt.
  - destruct i; discriminate.
  - destruct i; simpl in *.
    + inversion Hnth; subst. lia.
    + specialize (IH i OLD NEW Hnth Hlt). lia.
Qed.

(* ---------- The heart: every flow strictly reduces open demand ----- *)

Lemma step_decreases : forall m m' : mesh,
  step m m' -> gapcount m' < gapcount m.
Proof.
  intros m m' H. inversion H; subst.
  unfold gapcount; simpl.
  eapply total_replace_lt.
  - eassumption.
  - simpl. apply remove_lt. assumption.
Qed.

(* ================================================================== *)
(*  THEOREM 1 — CONVERGENCE                                            *)
(*  The step relation is well-founded: no infinite osmosis sequence    *)
(*  exists. Every mesh settles.                                        *)
(* ================================================================== *)

Theorem convergence : well_founded (fun m' m : mesh => step m m').
Proof.
  apply well_founded_lt_compat with (f := gapcount).
  intros x y H. apply step_decreases. exact H.
Qed.

(* ---------- Equilibrium, and its quantitative bound ---------- *)

Definition equilibrium (m : mesh) : Prop := forall m', ~ step m m'.

(* Any chain of flows starting at m. *)
Inductive chain : mesh -> nat -> Prop :=
| chain0 : forall m, chain m 0
| chainS : forall m m' n, step m m' -> chain m' n -> chain m (S n).

(* COROLLARY (quantitative convergence): a mesh with g open gaps       *)
(* reaches equilibrium in at most g flows.                             *)
Theorem chain_bound : forall m n, chain m n -> n <= gapcount m.
Proof.
  intros m n H. induction H.
  - lia.
  - pose proof (step_decreases _ _ H). lia.
Qed.

(* A mesh with zero open gaps is already at equilibrium:              *)
(* silence is a fixpoint, not a failure.                              *)
Lemma total_zero_nth : forall (l : list twin) (i : nat) (T : twin),
  total l = 0 -> nth_error l i = Some T -> length (gaps T) = 0.
Proof.
  induction l as [| h t IH]; intros i T Hz Hn; destruct i; simpl in *.
  - discriminate.
  - discriminate.
  - inversion Hn; subst. lia.
  - eapply IH; [lia | eauto].
Qed.

Theorem zero_is_equilibrium : forall m, gapcount m = 0 -> equilibrium m.
Proof.
  intros m Hz m' Hs. inversion Hs; subst.
  assert (Hlen : length (gaps B) = 0)
    by (eapply total_zero_nth; [exact Hz | eassumption]).
  destruct (gaps B); simpl in *.
  - contradiction.
  - discriminate.
Qed.

(* ================================================================== *)
(*  Sanity demo: the maya/raj mesh from Spec §8.                       *)
(*  Fact 1 = eta(dinner). maya holds it; raj seeks it.                 *)
(* ================================================================== *)

Definition maya : twin := Twin [1] [].
Definition raj  : twin := Twin []  [1].
Definition m0   : mesh := Mesh [maya; raj] (fun _ _ _ => true).

Example demo_gapcount : gapcount m0 = 1.
Proof. reflexivity. Qed.

Example demo_flow_exists : exists m1, step m0 m1.
Proof.
  eexists. eapply (flow m0 0 1 maya raj 1).
  - reflexivity.
  - reflexivity.
  - simpl. left. reflexivity.
  - simpl. left. reflexivity.
  - reflexivity.
Qed.

(* And by chain_bound, m0 reaches equilibrium in at most 1 flow. *)

(* ---------- Trust, but verify the verifier ---------- *)
Print Assumptions convergence.
Print Assumptions chain_bound.
Print Assumptions zero_is_equilibrium.
