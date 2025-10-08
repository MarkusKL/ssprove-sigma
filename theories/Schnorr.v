
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

(*#[local] Open Scope F_scope.*)

From Project Require Import Scheme.

#[local] Open Scope ring_scope.
Import GroupScope.


Section Schnorr.

Context (G : CyclicGroup).

Definition schnorr : sigma :=
  {| Statement := 'fin #|el G|
   ; Witness := 'fin #|exp G|
   ; Message := 'fin #|el G|
   ; State := 'fin #|exp G|
   ; Challenge := 'fin #|exp G|
   ; Response := 'fin #|exp G|

   ; R :=
      (λ h w, otf h == (g G ^+ otf w))%bool
   ; commit := λ h w, {code
       r ← sample uniform #|exp G| ;;
       ret (fto (g G ^+ otf r), r)
     }
   ; response := λ h w a r e, {code
       ret (fto (otf r + otf w * otf e))
     }
   ; simulate := λ h e, {code
       z ← sample uniform #|exp G| ;;
       ret (fto (g G ^+ otf z * (otf h ^- otf e)), z)
     }
   ; verify := λ h a e z,
     (g G ^+ otf z == otf a * otf h ^+ otf e)%bool
   ; extractor := λ h a e e' z z',
     Some (fto ((otf z - otf z') / (otf e - otf e')))
  |}.

Theorem schnorr_Correct A
  `{ValidPackage (loc A) (ICorrect schnorr) A_export A} :
  AdvOf (Correct schnorr) A = 0.
Proof.
  eapply prove_perfect; [| eassumption ].
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel hwe.
  destruct hwe as [[h w] e].
  ssprove_sync => /eqP -> {h}.
  apply r_const_sample_L => [|a].
  1: apply LosslessOp_uniform.
  apply r_ret => s0 s1 H'.
  split; [ apply /eqP | assumption ].
  rewrite !otf_fto expg_modq expgD expg_modq expgM //.
Qed.

#[local] Definition f (e w : 'fin #|exp G|) :
  Arit (uniform #|exp G|) → Arit (uniform #|exp G|) :=
  λ z, fto (otf z + otf e * otf w).

Lemma bij_f w e : bijective (f w e).
Proof.
  unfold f.
  exists (λ x, fto (otf x - otf w * otf e)).
  1,2: intros x; rewrite otf_fto ?GRing.addrK ?GRing.subrK fto_otf //.
Qed.

Theorem schnorr_SHVZK A
  `{ValidPackage (loc A) (ITranscript schnorr) A_export A} :
  AdvOf (SHVZK schnorr) A = 0.
Proof.
  eapply prove_perfect; [| eassumption ].
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel hwe.
  destruct hwe as [[h w] e].
  rewrite -(fto_otf h) -(fto_otf e).
  move: (otf w) (otf h) (otf e) => {}w {}h {}e.
  rewrite 2!otf_fto.
  ssprove_sync_eq => /eqP -> {h}.
  eapply r_uniform_bij with (1 := bij_f (fto w) (fto e)) => z.
  apply r_ret.

  intros s₀ s₁ Hs.
  split; [| assumption ].
  do 2 f_equal.
  1,2: rewrite /f !otf_fto //=.
  rewrite expg_modq expgD -mulgA -expgM expg_modq mulgV mulg1 //.
Qed.

Theorem schnorr_Special_Soundness A
  `{ValidPackage (loc A) (ISoundness schnorr) A_export A} :
  AdvOf (Special_Soundness schnorr) A = 0.
Proof.
  eapply prove_perfect; [| eassumption ].
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel h.
  destruct h as [[[h R] [e1 z1]] [e2 z2]].
  ssprove_sync => /eqP H1.
  ssprove_sync => /eqP H2.
  ssprove_sync => /eqP H3.
  apply r_ret => s0 s1 H'.
  split; [| assumption ].

  symmetry.
  apply /eqP.
  rewrite otf_fto expg_frac expg_sub.
  rewrite mulgC.
  rewrite H1 H2 invMg.
  rewrite mulgA.
  rewrite -(mulgA _ _ (otf R)) mulVg mulg1.
  rewrite (mulgC _ (_ ^+ _)).
  rewrite -expg_sub -expg_frac.
  rewrite expg_fracgg //.
  apply /eqP => H4.
  apply GRing.subr0_eq in H4.
  apply (f_equal fto) in H4.
  rewrite 2!fto_otf // in H4.
Qed.

End Schnorr.
