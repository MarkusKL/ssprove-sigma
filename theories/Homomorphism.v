
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From SSProve.Crypt Require Import NominalPrelude.
Import PackageNotation.
#[local] Open Scope package_scope.

(*#[local] Open Scope F_scope.*)

From Project Require Import Scheme.

#[local] Open Scope ring_scope.
Import GroupScope.

Instance finGroupPositive {G : finGroupType} : Positive #|G|.
Proof. apply /card_gt0P. by exists 1. Qed.

(* Challenge space can only be ranges [0, C-1].
   Will this be problem? *)

Module Type HomArgs.
  Parameter (G H : finGroupType).
  Parameter (C : positive).
  Parameter (F : H → G → H).
  Parameter (l : nat).
  Parameter (u : G).
  Parameter (Hom : ∀ h x y, F h (x * y) = F h x * F h y).
  Parameter (Thm3a : ∀ e e' : 'fin C, e != e' → gcdz l (e%:Z  - e'%:Z) = 1%Z).
  Parameter (Thm3b : ∀ h, F h u = h ^+ l). (* same h? *)
End HomArgs.


Module Homomorphism (Args : HomArgs).

Import Args.

Notation "x ⊗  y" :=
  (@mulg H x y) (at level 40).

Notation "x ∗ y" :=
  (@mulg G x y) (at level 40).

Lemma Hom1 {h} : F h 1 = 1.
Proof.
  apply (mulgI (F h 1)).
  rewrite -Hom 2!mulg1 //.
Qed.

Lemma Hom_invg {h} {x : G} : F h x^-1 = (F h x)^-1.
Proof.
  apply (mulgI (F h x)).
  rewrite -Hom mulgV mulgV Hom1 //.
Qed.

Lemma Hom_expgn {h} {x : G} {n} : F h (x ^+ n) = F h x ^+ n.
Proof.
  induction n.
  - rewrite 2!expg0 Hom1 //.
  - rewrite 2!expgS Hom IHn //.
Qed.

Definition expgz {G : finGroupType} : G → int → G := λ g z,
  match z with
  | Posz n => g ^+ n
  | Negz n => g ^- n.+1
  end.

Notation "x ^ z" :=
  (expgz x z) : group_scope.

Lemma expgz_pos {G : finGroupType} {x : G} {n} : x ^+ n = x ^ (n%:Z).
Proof. done. Qed.

Lemma expgz_neg {G : finGroupType} {x : G} {n} : x ^- n = x ^ (- n%:Z).
Proof. destruct n => //=. rewrite expg0 invg1 //. Qed.

Lemma expgzD1 {G : finGroupType} {x : G} {z : int}
  : x ^ (1 + z) = x * x ^ z.
Proof.
  destruct z => /=.
  - rewrite add1n expgS //.
  - rewrite {1}NegzE intS.
    rewrite -expgVn expgS expgVn.
    rewrite GRing.opprD GRing.addrA.
    rewrite GRing.subrr GRing.add0r.
    rewrite mulKVg expgz_neg //.
Qed.

Lemma expgz_neg1 {G : finGroupType} {x : G} {z : int} : x^-1 ^ (- z) = x ^ z.
Proof.
  destruct z.
  - rewrite -expgz_neg -expgVn invgK //.
  - rewrite NegzE GRing.opprK -expgz_pos.
    rewrite -expgz_neg -expgVn //.
Qed.

Lemma expgzDn {G : finGroupType} {x : G} {n : nat} {z' : int}
  : x ^ (n%:Z + z') = x ^+ n * x ^ z'.
Proof.
  induction n => /=.
  - rewrite GRing.add0r expg0 mul1g //.
  - rewrite intS -GRing.addrA.
    rewrite expgzD1 IHn mulgA expgS //.
Qed.

Lemma expgzD {G : finGroupType} {x : G} {z z' : int}
  : x ^ (z + z') = x ^ z * x ^ z'.
Proof.
  destruct z; [ by rewrite expgzDn |].
  rewrite NegzE -expgz_neg1.
  rewrite GRing.opprD GRing.opprK expgzDn.
  rewrite -expgz_neg expgVn expgz_neg1 //.
Qed.

Lemma expgzMn {G : finGroupType} {x : G} {z : int} {n : nat}
  : x ^ (z * n%:Z) = (x ^ z) ^+ n.
Proof.
  induction n.
  - by rewrite GRing.mulr0 /= 2!expg0.
  - rewrite intS.
    rewrite GRing.mulrDr GRing.mulr1.
    rewrite expgzD IHn -expgS //.
Qed.

Lemma expgzM {G : finGroupType} {x : G} {z z' : int}
  : x ^ (z * z') = (x ^ z) ^ z'.
Proof.
  destruct z'; [ by rewrite expgzMn |].
  rewrite NegzE GRing.mulrN.
  rewrite -expgz_neg1 GRing.opprK expgzMn.
  rewrite -expgz_neg -expgVn /=.
  f_equal. destruct z; by rewrite /= expgVn.
Qed.

Lemma Hom_expgz {h} {x : G} {z} : F h (x ^ z) = F h x ^ z.
Proof.
  destruct z => /=.
  - rewrite Hom_expgn //.
  - rewrite Hom_invg Hom_expgn //.
Qed.


Definition homomorphism : sigma :=
  {| Statement := 'fin #|H|
   ; Witness := 'fin #|G|
   ; Message := 'fin #|H|
   ; State := 'fin #|G|
   ; Challenge := 'fin C
   ; Response := 'fin #|G|

   ; R :=
      (λ h w, otf h == (F (otf h) (otf w)))%bool
   ; commit := λ h w, {code
       r ← sample uniform #|G| ;;
       ret (fto (F (otf h) (otf r)), r)
     }
   ; response := λ h w a r e, {code
       ret (fto (otf r ∗ otf w ^+ e))
     }
   ; verify := λ h a e z,
     (F (otf h) (otf z) == otf a ⊗ otf h ^+ e)%bool
   ; simulate := λ h e, {code
       z ← sample uniform #|G| ;;
       ret (fto (F (otf h) (otf z) ⊗ otf h ^- e), z)
     }
   ; extractor := λ h _ e e' z z',
       let (a, b) := egcdz l (e%:Z - e'%:Z) in
       Some (fto (u ^ a ∗ ((otf z')^-1 ∗ otf z) ^ b))
  |}.

Theorem hom_Correct A
  `{ValidPackage (loc A) (ICorrect homomorphism) A_export A} :
  AdvOf (Correct homomorphism) A = 0.
Proof.
  eapply prove_perfect; [| eassumption ].
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel hwe.
  destruct hwe as [[h w] e].
  ssprove_sync => /eqP {3}->.
  apply r_const_sample_L => [|a].
  1: apply LosslessOp_uniform.
  apply r_ret => s0 s1 H'.
  split; [ apply /eqP | assumption ].
  (* CHANGED depends on F beign a group homomorphism *)
  rewrite !otf_fto Hom Hom_expgn //.
  (* END *)
Qed.

#[local] Definition f (x : G) :
  Arit (uniform #|G|) → Arit (uniform #|G|) :=
  λ z, fto (otf z ∗ x).

Lemma bij_f x : bijective (f x).
Proof.
  unfold f.
  exists (λ y, fto (otf y ∗ x^-1)).
  1,2: intros y; rewrite otf_fto ?mulgK ?mulgKV fto_otf //.
Qed.

Theorem hom_SHVZK A
  `{ValidPackage (loc A) (ITranscript homomorphism) A_export A} :
  AdvOf (SHVZK homomorphism) A = 0.
Proof. (* only relies on group homomorphism *)
  eapply prove_perfect; [| eassumption ].
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel hwe.
  destruct hwe as [[h w] e].
  rewrite -(fto_otf h) (* -(fto_otf e) *).
  move: (otf w) (otf h) (*(otf e)*) => {}w {}h (*{}e*).
  rewrite otf_fto.
  ssprove_sync_eq => /eqP {3}->.
  eapply r_uniform_bij with (1 := bij_f (w ^+ e)) => z.
  apply r_ret.

  intros s₀ s₁ Hs.
  split; [| assumption ].
  do 2 f_equal.
  rewrite /f !otf_fto //=.
  rewrite Hom Hom_expgn mulgK //.
Qed.
(* Instance dependent commitment *)

Theorem hom_Special_Soundness A
  `{ValidPackage (loc A) (ISoundness homomorphism) A_export A} :
  AdvOf (Special_Soundness homomorphism) A = 0.
Proof.
  eapply prove_perfect; [| eassumption ].
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel h.
  destruct h as [[[h R] [e1 z1]] [e2 z2]].
  ssprove_sync => /eqP H1.
  ssprove_sync => /eqP H2.
  ssprove_sync => H3.
  apply r_ret => s0 s1 H'.
  split; [| assumption ].

  symmetry.
  case: (@egcdzP l (e1%:Z - e2%:Z)) => a b E1 E2.
  apply /eqP.
  rewrite otf_fto Hom 2!Hom_expgz Hom Hom_invg.
  rewrite H1 H2.
  rewrite (Thm3b (otf h)).
  rewrite invMg mulgA mulgKV.
  rewrite expgz_neg 2!expgz_pos.
  rewrite -expgzM -expgzD -expgzM -expgzD.
  rewrite -{1}(expg1 (otf h)) expgz_pos.
  f_equal.
  rewrite -(GRing.addrC e1%:Z).
  rewrite (GRing.mulrC) (GRing.mulrC _ b).
  rewrite E1 Thm3a //.
Qed.

End Homomorphism.


Lemma gcdz_prime {p : nat} {d : int}
  : prime p → (0 < `|d|%Z < p)%N → gcdz p d = 1%Z.
Proof.
  move=> Hp /andP Hd.
    rewrite -(GRing.mulr1 d).
  rewrite Gauss_gcdzr ?gcdz1 //.
  rewrite coprimezE /=.
  rewrite prime_coprime //.
  rewrite gtnNdvd //; apply Hd.
Qed.

Lemma absz_sub {e e' l : nat} : (e < l)%N → (e' < l)%N → (`|e - e'| < l)%N.
Proof.
  cut (∀ e e', (e < l)%N → (e' < l)%N → (0 <= e%:Z - e'%:Z) → (`|e - e'| < l)%N).
  - intros H H1 H2.
    destruct (0 <= e%:Z - e'%:Z)%Z eqn:E.
    + rewrite H //.
    + rewrite distnC H //.
      rewrite -GRing.opprB.
      rewrite Num.Theory.lerNr.
      rewrite GRing.oppr0.
      rewrite Num.Theory.real_leNgt //=.
      apply /negP => H'.
      move: E => /negP E.
      apply E.
      by apply Order.POrderTheory.ltW.
  - move=> {}e {}e' He He' H.
    rewrite -ltz_nat gez0_abs //.
    rewrite Num.Theory.ltrBlDl.
    rewrite Num.Theory.ltr_wpDl //.
Qed.

Lemma gcdz_prime_diff {p n n' : nat}
  : prime p → n != n' → (n < p)%N → (n' < p)%N → gcdz p (n%:Z - n'%:Z) = 1%Z.
Proof.
  intros Hp H Hn Hn'.
  rewrite gcdz_prime //.
  apply /andP; split.
  - move: H => /eqP H.
    rewrite lt0n.
    rewrite absz_eq0.
    apply /negP => /eqP H'.
    apply GRing.Theory.subr0_eq in H'.
    move: H' => /eqP.
    by rewrite eqz_nat => /eqP H'.
  - rewrite absz_sub //.
Qed.


(* Schnorr instantiation *)
From SSProve.Crypt Require Import CyclicGroup.

Axiom (CG : CyclicGroup).

Instance Positive_q : Positive (q CG).
Proof. rewrite -trunc_q //. Qed.

Module SchnorrArgs : HomArgs.
  Definition G : finGroupType := exp CG.
  Definition H : finGroupType := el CG.
  Definition C : positive := mkpos (q CG).
  Definition F : H → G → H := λ _ x, g CG ^+ x.
  Definition l : nat := q CG.
  Definition u : G := 1.

  Lemma Hom : ∀ h x y, F h (x * y) = F h x * F h y.
  Proof.
    intros h x y.
    rewrite /F -expgD expg_modq //.
  Qed.

  Lemma Thm3a : ∀ e e' : 'fin C, e != e' → gcdz l (e%:Z - e'%:Z) = 1%Z.
  Proof.
    intros e e' H.
    apply gcdz_prime_diff => //.
    apply prime_order.
  Qed.

  Lemma Thm3b : ∀ h, F h u = h ^+ l.
  Proof.
    intros h.
    rewrite expgq //.
  Qed.
End SchnorrArgs.

Module Schnorr := Homomorphism SchnorrArgs.
Print Schnorr.homomorphism.
Check Schnorr.hom_SHVZK.
(* Recursive Extraction Schnorr.homomorphism. *)


