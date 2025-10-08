
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

From SSProve.Crypt Require Import NominalPrelude CyclicGroup.
Import PackageNotation.
#[local] Open Scope package_scope.

Import GroupScope.
#[local] Open Scope F_scope.

Lemma destruct_let_pair [A B C] (xy : A * B) (f : A → B → C) :
  (let (x, y) := xy in f x y) = f xy.1 xy.2.
Proof. by destruct xy. Qed.

Definition rel_jdg_replace_l
  (A B : choiceType) (pre : precond) (post : postcond A B)
  (l l' : raw_code A) (r : raw_code B)
    (Rest : ⊢ ⦃ pre ⦄ l ≈ r ⦃ post ⦄)
    (Left : l = l')
     : ⊢ ⦃ pre ⦄ l' ≈ r ⦃ post ⦄ :=
  (rel_jdg_replace _ _ _ _ _ _ _ _ Rest Left Logic.eq_refl).

Definition rel_jdg_replace_r
  (A B : choiceType) (pre : precond) (post : postcond A B)
  (l : raw_code A) (r r' : raw_code B)
    (Rest : ⊢ ⦃ pre ⦄ l ≈ r ⦃ post ⦄)
    (Right : r = r')
     : ⊢ ⦃ pre ⦄ l ≈ r' ⦃ post ⦄ :=
  (rel_jdg_replace _ _ _ _ _ _ _ _ Rest Logic.eq_refl Right).

Definition rel_jdg_replace_sem_l
  (A B : choiceType) (pre : precond) (post : postcond A B)
  (l l' : raw_code A) (r : raw_code B)
    (Rest : ⊢ ⦃ pre ⦄ l ≈ r ⦃ post ⦄)
    (Left : ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ l ≈ l' ⦃ eq ⦄)
     : ⊢ ⦃ pre ⦄ l' ≈ r ⦃ post ⦄ :=
  (rel_jdg_replace_sem _ _ _ _ _ _ _ _ Rest Left (rreflexivity_rule _)).

Definition rel_jdg_replace_sem_r
  (A B : choiceType) (pre : precond) (post : postcond A B)
  (l : raw_code A) (r r' : raw_code B)
    (Rest : ⊢ ⦃ pre ⦄ l ≈ r ⦃ post ⦄)
    (Right : ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ r ≈ r' ⦃ eq ⦄)
     : ⊢ ⦃ pre ⦄ l ≈ r' ⦃ post ⦄ :=
  (rel_jdg_replace_sem _ _ _ _ _ _ _ _ Rest (rreflexivity_rule _) Right).

Lemma fseparate_neq:
  ∀ {T : ordType} {S : Type} {m m' : {fmap T → S}} {l l' : T * S},
    fseparate m m' → fhas m l → fhas m' l' → l.1 != l'.1.
Proof.
  intros T S m m' l l' H1 H2 H3.
  apply fseparateE in H1.
  move: H1 => /fdisjointP H1.
  apply fhas_in in H2, H3.
  apply /eqP => H4.
  specialize (H1 _ H2).
  move: H1 => /negP.
  by rewrite H4.
Qed.

Lemma swap_code_aux :
  ∀ A B (c₀ : raw_code A) (c₁ : raw_code B) (L₀ L₁ : Locations),
    fseparate L₀ L₁ →
    ValidCode L₀ [interface] c₀ →
    ValidCode L₁ [interface] c₁ →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
        a₀ ← c₀ ;; a₁ ← c₁ ;; ret (a₀, a₁)
      ≈ a₁ ← c₁ ;; a₀ ← c₀ ;; ret (a₀, a₁)
      ⦃ eq ⦄.
Proof.
  move=> A B c₀ c₁ L₀ L₁ Disj V₀ V₁.
  induction V₀.
  all: ssprove_code_simpl; simpl.
  - apply rreflexivity_rule.
  - exfalso. eapply fhas_empty. eassumption.
  - ssprove_swap_rhs 0%N.
    2: ssprove_sync_eq; apply H1.
    clear H1.
    induction V₁; simpl.
    + apply rreflexivity_rule.
    + exfalso. eapply fhas_empty. eassumption.
    + ssprove_swap_lhs 0%N.
      ssprove_sync_eq => x.
      apply H3.
    + pose proof (fseparate_neq Disj H H1).
      ssprove_swap_lhs 0%N.
      by ssprove_sync_eq.
    + ssprove_swap_lhs 0%N.
      by ssprove_sync_eq.
  - ssprove_swap_rhs 0%N.
    2: ssprove_sync_eq; apply IHV₀.
    clear IHV₀.
    induction V₁; simpl.
    + apply rreflexivity_rule.
    + exfalso. eapply fhas_empty. eassumption.
    + apply fseparateC in Disj.
      pose proof (fseparate_neq Disj H0 H).
      ssprove_swap_lhs 0%N.
      by ssprove_sync_eq.
    + apply fseparateC in Disj.
      pose proof (fseparate_neq Disj H0 H).
      ssprove_swap_lhs 0%N.
      ssprove_sync_eq.
      apply IHV₁.
    + ssprove_swap_lhs 0%N.
      by ssprove_sync_eq.
  - ssprove_swap_rhs 0%N.
    by ssprove_sync_eq => H'.
Qed.

Theorem swap_code :
  ∀ A B C (c₀ : raw_code A) (c₁ : raw_code B)
    (r : A -> B -> raw_code C) (L₀ L₁ : Locations),
    fseparate L₀ L₁ →
    ValidCode L₀ [interface] c₀ →
    ValidCode L₁ [interface] c₁ →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
        a₀ ← c₀ ;; a₁ ← c₁ ;; r a₀ a₁ ≈ a₁ ← c₁ ;; a₀ ← c₀ ;; r a₀ a₁
      ⦃ eq ⦄.
Proof.
  intros A B C c0 c1 r L0 L1 Disj V0 V1.
  eapply rswap_ruleR.
  1: easy.
  1: intros a0 a1; apply rsym_pre; [ easy | apply rreflexivity_rule ].
  eapply swap_code_aux.
  1: exact Disj.
  all: easy.
Qed.

Theorem rswap_scheme [A B C : choice_type]
  (c₀ : raw_code A) (c₁ : raw_code B) (r : A -> B -> raw_code C) :
  ValidCode emptym [interface] c₀ →
  ValidCode emptym [interface] c₁ →
  ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
      a₀ ← c₀ ;; a₁ ← c₁ ;; r a₀ a₁ ≈ a₁ ← c₁ ;; a₀ ← c₀ ;; r a₀ a₁
    ⦃ eq ⦄.
Proof. apply swap_code. fmap_solve. Qed.

#[export] Hint Extern 50 (_ = code_link _ _) =>
  rewrite code_link_scheme
  : ssprove_code_simpl.
