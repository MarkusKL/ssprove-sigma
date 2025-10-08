
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

From Project Require Import Extra Scheme.

#[local] Open Scope ring_scope.
Import GroupScope.


Section OR.

Context (G : CyclicGroup).

Record or_params :=
  { left : sigma
  ; right : sigma
  ; left_challenge : Challenge left = 'fin #|exp G|
  ; right_challenge : Challenge right = 'fin #|exp G|
  }.

Implicit Type (p : or_params).

Definition into {T S : choice_type} (H : S = T) : T → S.
Proof. rewrite H. exact id. Defined.

Definition pad p : 'fin #|exp G| → Challenge p.(left) → Challenge p.(right).
Proof.
  rewrite p.(left_challenge) p.(right_challenge) => c c1.
  exact (fto (otf c1 + otf c)).
Defined.

Definition unpad p : 'fin #|exp G| → Challenge p.(right) → Challenge p.(left).
Proof.
  rewrite p.(left_challenge) p.(right_challenge) => c c2.
  exact (fto (otf c2 - otf c)).
Defined.

Definition or p : sigma :=
  {| Statement := Statement p.(left) × Statement p.(right)
   ; Witness := (Witness p.(left) + Witness p.(right))%type
   ; Message := Message p.(left) × Message p.(right)
   ; State :=
     ((State p.(left) × Challenge p.(right) × Response p.(right))
     + (State p.(right) × Challenge p.(left) × Response p.(left)))%type
   ; Challenge := 'fin #|exp G|
   ; Response :=
       ((Challenge p.(left) × Response p.(left))
       × Challenge p.(right)) × Response p.(right)

   ; R := λ '(h1, h2) w,
       match w with
       | inl w1 => p.(left).(R) h1 w1
       | inr w2 => p.(right).(R) h2 w2
       end

   ; commit := λ '(h1, h2) w,
      match w with
      | inl wl => {code
          '(R1, st1) ← p.(left).(commit) h1 wl ;;
          c2 ← sample uniform #|exp G| ;;
          let c2 := into p.(right_challenge) c2 in
          '(R2, s2) ← p.(right).(simulate) h2 c2 ;;
          ret ((R1, R2), inl (st1, c2, s2))
        }
      | inr wr => {code
          '(R2, st2) ← p.(right).(commit) h2 wr ;;
          c1 ← sample uniform #|exp G| ;;
          let c1 := into p.(left_challenge) c1 in
          '(R1, s1) ← p.(left).(simulate) h1 c1 ;;
          ret ((R1, R2), inr (st2, c1, s1))
        }
      end
   ; response := λ '(h1, h2) w '(a1, a2) st c,
      match w, st with
      | inl w1, inl (st1, c2, s2) => {code
          let c1 := unpad p c c2 in
          s1 ← p.(left).(response) h1 w1 a1 st1 c1 ;;
          ret (c1, s1, c2, s2)
        }
      | inr w2, inr (st2, c1, s1) => {code
          let c2 := pad p c c1 in
          s2 ← p.(right).(response) h2 w2 a2 st2 c2 ;;
          ret (c1, s1, c2, s2)
        }
      | _, _ => {code fail }
      end
   ; simulate := λ '(h1, h2) c,
     {code
       c1 ← sample uniform #|exp G| ;;
       let c1 := into p.(left_challenge) c1 in
       let c2 := pad p c c1 in
       '(R1, s1) ← p.(left).(simulate) h1 c1 ;;
       '(R2, s2) ← p.(right).(simulate) h2 c2 ;;
       ret ((R1, R2), (c1, s1, c2, s2))
     }
   ; verify := λ '(h1, h2) '(R1, R2) c z,
      let '(c1, s1, c2, s2) := z in
      p.(left).(verify) h1 R1 c1 s1
      && p.(right).(verify) h2 R2 c2 s2
      && (pad p c c1 == c2)
   ; extractor := λ '(h1, h2) '(R1, R2) e e' z z',
      let '(c1, s1, c2, s2) := z in
      let '(c1', s1', c2', s2') := z' in
      if c1 != c1' then
        omap inl
          (p.(left).(extractor) h1 R1 c1 c1' s1 s1')
      else
        omap inr
          (p.(right).(extractor) h2 R2 c2 c2' s2 s2')
  |}.


Definition ROUTE n m S T : package
    [interface [ m ] : { S ~> T }]
    [interface [ n ] : { S ~> T }] :=
  [package emptym ;
    [ n ] (s) {
      t ← call [ m ] s ;;
      ret t
    }
  ].

Definition LEFT := 0%N.
Definition RIGHT := 1%N.

Definition Exp {I E} : package I E → Interface := λ _, E.

Definition Left p :=
  (ROUTE LEFT TRANSCRIPT
    (Input p.(left))
    (p.(left).(Message) × p.(left).(Response))
  ).

Definition Right p :=
  (ROUTE RIGHT TRANSCRIPT
    (Input p.(right))
    (p.(right).(Message) × p.(right).(Response))
  ).

Definition SHVZK_call p :
  package (unionm (Exp (Left p)) (Exp (Right p))) (ITranscript (or p)) :=
  [package emptym ;
    [ TRANSCRIPT ] '((h1, h2), w, c) {
      c1 ← sample uniform #|exp G| ;;
      let c1 := into p.(left_challenge) c1 in
      let c2 := pad p c c1 in
      match w with
      | inl w1 =>
        '(R1, s1) ← call [ LEFT ] (h1, w1, c1) ;;
        '(R2, s2) ← p.(right).(simulate) h2 c2 ;;
        ret ((R1, R2), (c1, s1, c2, s2))
      | inr w2 =>
        '(R1, s1) ← p.(left).(simulate) h1 c1 ;;
        '(R2, s2) ← call [ RIGHT ] (h2, w2, c2) ;;
        ret ((R1, R2), (c1, s1, c2, s2))
      end
    }
  ].

Notation CALL p L R :=
  ( (SHVZK_call p) ∘ ( (Left p ∘ L) || (Right p ∘ R)) )%sep.

Definition iso p (c : 'fin #|exp G|)
  : Arit (uniform #|exp G|) → Arit (uniform #|exp G|)
  := λ c2, fto (otf c2 - otf c).

Lemma into_iso p c c2
  : into p.(left_challenge) (iso p c c2) = unpad p c (into p.(right_challenge) c2).
Proof.
  unfold into, unpad, iso, eq_rect_r.
  move: (Logic.eq_sym p.(left_challenge)) (Logic.eq_sym p.(right_challenge)).
  rewrite p.(left_challenge) p.(right_challenge) => H1 H2.
  rewrite -4!Eqdep.EqdepTheory.eq_rect_eq //.
Qed.

Lemma pad_unpad p c c2 : pad p c (unpad p c c2) = c2.
Proof.
  unfold pad, unpad, eq_rect_r.
  move: c2 (Logic.eq_sym p.(left_challenge)) (Logic.eq_sym p.(right_challenge)).
  rewrite p.(left_challenge) p.(right_challenge) => c2 H1 H2.
  rewrite -4!Eqdep.EqdepTheory.eq_rect_eq.
  rewrite otf_fto GRing.addrNK fto_otf //.
Qed.

Lemma iso_bij p c : bijective (iso p c).
Proof.
  unfold iso.
  exists (λ c1, fto (otf c1 + otf c)) => [c2|c1].
  + rewrite otf_fto GRing.addrNK fto_otf //.
  + rewrite otf_fto GRing.addrK fto_otf //.
Qed.

Lemma commit_call p :
  perfect (ITranscript (or p)) (SHVZK_real (or p))
    (CALL p (SHVZK_real p.(left)) (SHVZK_real p.(right))).
Proof.
  ssprove_share.
  eapply prove_perfect.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel hwe.
  destruct hwe as [[[h1 h2] [w1|w2]] c].
  - ssprove_code_simpl; simpl.
    simplify_linking.
    ssprove_code_simpl; simpl.
    ssprove_code_simpl_more.
    ssprove_swap_rhs 0%N.
    ssprove_sync => H'.
    ssprove_code_simpl; simpl.
    ssprove_swap_rhs 0%N.
    apply rsame_head => [[R1 st1]].
    eapply r_uniform_bij with (1 := iso_bij p c) => c2.
    eapply rel_jdg_replace_sem_r.
    2: eapply rswap_scheme; ssprove_valid.
    rewrite into_iso pad_unpad.
    apply rsame_head => [[v1 v2]].
    apply rsame_head => v3.
    by apply r_ret.
  - simpl; ssprove_code_simpl; simpl.
    eapply rel_jdg_replace_sem_r; simpl.
    2: {
      ssprove_sync_eq => ?.
      eapply rsame_head => x.
      rewrite destruct_let_pair.
      eapply @rreflexivity_rule.
    }
    ssprove_code_simpl_more.
    eapply rel_jdg_replace_sem_r; simpl.
    2: ssprove_sync_eq => ?.
    2: eapply rswap_scheme; ssprove_valid.
    ssprove_code_simpl_more.
    ssprove_swap_rhs 0%N.
    ssprove_sync_eq => HR.
    ssprove_code_simpl.
    ssprove_swap_rhs 0%N.
    apply rsame_head => [[a2 st2]].
    ssprove_sync_eq => e1.
    eapply rel_jdg_replace_sem_r; simpl.
    2: eapply rswap_scheme; ssprove_valid.
    ssprove_valid.
    apply rsame_head => [[a1 z1]].
    apply rsame_head => z2.
    by apply r_ret.
Qed.

Lemma simulate_call p :
  perfect (ITranscript (or p)) (SHVZK_ideal (or p))
    (CALL p (SHVZK_ideal p.(left)) (SHVZK_ideal p.(right))).
Proof.
  ssprove_share.
  eapply prove_perfect.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel hwe.
  destruct hwe as [[[h1 h2] [w1|w2]] c].
  - ssprove_code_simpl; simpl.
    simplify_linking.
    ssprove_code_simpl; simpl.
    ssprove_code_simpl_more.
    ssprove_swap_rhs 0%N.
    ssprove_sync_eq => HR.
    ssprove_sync_eq => e1.
    rewrite bind_assoc.
    apply rsame_head => [[a1 z1]] /=.
    apply rsame_head => [[a2 z2]] /=.
    by apply r_ret.
  - simpl; ssprove_code_simpl; simpl.
    ssprove_swap_lhs 0%N.
    ssprove_sync_eq => e1.

    eapply rel_jdg_replace_sem_r; simpl.
    2: {
      eapply rsame_head => ?.
      rewrite destruct_let_pair.
      eapply @rreflexivity_rule.
    }
    eapply rel_jdg_replace_sem_r; simpl.
    2: eapply rswap_scheme; ssprove_valid.
    ssprove_code_simpl_more.
    ssprove_sync_eq => HR.
    eapply rel_jdg_replace_sem_r; simpl.
    2: eapply rswap_scheme; ssprove_valid.
    apply rsame_head => [[a1 z1]] /=.
    rewrite bind_assoc.
    apply rsame_head => [[a2 z2]] /=.
    by apply r_ret.
Qed.

Definition A_left p A : nom_package :=
  (A ∘ SHVZK_call p) ∘ (Left p || (Right p ∘ SHVZK_real (right p))).

Definition A_right p A : nom_package :=
  (A ∘ SHVZK_call p) ∘ ((Left p ∘ SHVZK_ideal (left p)) || Right p).

Theorem OR_SHVZK p A
  `{ValidPackage (loc A) (ITranscript (or p)) A_export A} :
  ( AdvOf (SHVZK (or p)) A
    <= AdvOf (SHVZK p.(left)) (A_left p A)
     + AdvOf (SHVZK p.(right)) (A_right p A)
  )%R.
Proof.
  rewrite (Adv_perfect_l (commit_call p)).
  rewrite (Adv_perfect_r (simulate_call p)).
  ssprove_hop (CALL p (SHVZK_ideal p.(left)) (SHVZK_real p.(right))).
  rewrite 2!Adv_reduction.
  apply Num.Theory.lerD.
  - rewrite 2!sep_par_game_l.
    by rewrite Adv_reduction.
  - rewrite 2!sep_par_game_r.
    by rewrite Adv_reduction.
Qed.

End OR.
