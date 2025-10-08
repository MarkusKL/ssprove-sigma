
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

Section Scheme.

Record sigma :=
  { Statement : choice_type
  ; Witness : choice_type
  ; Message : choice_type
  ; State : choice_type
  ; Challenge : choice_type
  ; Response : choice_type

  ; R : Statement → Witness → bool

  ; commit :
    ∀ (h : Statement) (w : Witness),
      code emptym [interface] (Message × State)

  ; response :
    ∀ (h : Statement) (w : Witness)
      (a : Message) (s : State) (e : Challenge),
      code emptym [interface] Response

  ; verify :
    ∀ (h : Statement) (a : Message) (e : Challenge)
      (z : Response),
      bool

  ; simulate :
    ∀ (h : Statement) (e : Challenge),
      code emptym [interface] (Message × Response)

  ; extractor :
    ∀ (h : Statement) (a : Message)
      (e : Challenge) (e' : Challenge)
      (z : Response) (z' : Response),
      'option Witness
  }.


(* Section: Correct *)

Definition Input p : choice_type
  := p.(Statement) × p.(Witness) × p.(Challenge).

Definition RUN : nat := 1.

Definition ICorrect p :=
  [interface [ RUN ] : { Input p ~> bool } ].

Definition Correct_real p :
  game (ICorrect p) :=
  [package emptym ;
    [ RUN ] '(h, w, e) {
      #assert p.(R) h w ;;
      '(a, s) ← p.(commit) h w ;;
      z ← p.(response) h w a s e ;;
      ret (p.(verify) h a e z)
    }
  ].

Definition Correct_ideal p :
  game (ICorrect p) :=
  [package emptym ;
    [ RUN ] '(h, w, e) {
      #assert p.(R) h w ;;
      ret true
    }
  ].

Definition Correct p b :=
  if b then Correct_real p else Correct_ideal p.


(* Section: SHVZK *)

Definition TRANSCRIPT : nat := 0.

Definition ITranscript p := 
  [interface [ TRANSCRIPT ] : { Input p ~> p.(Message) × p.(Response) } ].

Definition SHVZK_real p :
  game (ITranscript p) :=
  [package emptym ;
    [ TRANSCRIPT ] '(h, w, e) {
      #assert p.(R) h w ;;
      '(a, s) ← p.(commit) h w ;;
      z ← p.(response) h w a s e ;;
      ret (a, z)
    }
  ].

Definition SHVZK_ideal p :
  game (ITranscript p) :=
  [package emptym ;
    [ TRANSCRIPT ] '(h, w, e) {
      #assert p.(R) h w ;;
      '(a, z) ← p.(simulate) h e ;;
      ret (a, z)
    }
  ].

Definition SHVZK p b :=
  if b then SHVZK_real p else SHVZK_ideal p.


(* Section: Relating SHVZK and correctness *)

Definition Verify_call p :
  package (ITranscript p) (ICorrect p) :=
  [package emptym ;
    [ RUN ] '(h, w, e) {
      '(a, z) ← call [ TRANSCRIPT ] (h, w, e) ;;
      ret (p.(verify) h a e z)
    }
  ].

Lemma Verify_SHVZK_Correct_perf p
  : perfect (ICorrect p) (Verify_call p ∘ SHVZK_real p) (Correct_real p).
Proof.
  ssprove_share.
  eapply prove_perfect.
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel hwe.
  ssprove_code_simpl.
  destruct hwe as [[h w] e].
  ssprove_code_simpl_more.
  ssprove_sync_eq => _.
  ssprove_code_simpl.
  eapply rsame_head => as'.
  move: as' => [a s].
  eapply rsame_head => z.
  eapply r_ret; auto.
Qed.

Definition Correct_sim p := (Verify_call p ∘ SHVZK_ideal p)%sep.

Lemma Adv_Correct_sim p A
  `{ValidPackage (loc A) (ICorrect p) A_export A} :
  (Adv (Correct_sim p) (Correct_ideal p) A
    <= AdvOf (SHVZK p) (A ∘ Verify_call p) + AdvOf (Correct p) A)%R.
Proof.
  ssprove_hop (Verify_call p ∘ SHVZK_real p)%sep.
  apply Num.Theory.lerD.
  + rewrite Adv_reduction Adv_sym //.
  + ssprove_hop (Correct_real p).
    rewrite Verify_SHVZK_Correct_perf.
    rewrite GRing.add0r //.
Qed.

(* Section: 2-special-soundness *)

Definition SOUNDNESS : nat := 4.

Definition Opening p := p.(Challenge) × p.(Response).
Definition Soundness p :=
  p.(Statement) × p.(Message) × Opening p × Opening p.

Definition ISoundness p :=
  [interface [ SOUNDNESS ] : { Soundness p ~> 'bool } ].

Definition Special_Soundness_f p : game (ISoundness p) :=
  [package emptym ;
    [ SOUNDNESS ] '(h, a, (e, z), (e', z')) {
      #assert p.(verify) h a e z ;;
      #assert p.(verify) h a e' z' ;;
      #assert (e != e') ;;
      let ow := p.(extractor) h a e e' z z' in
      ret (if ow is Some w then p.(R) h w else false)
    }
  ].

Definition Special_Soundness_t p : game (ISoundness p) :=
  [package emptym ;
    [ SOUNDNESS ] '(h, a, (e, z), (e', z')) {
      #assert p.(verify) h a e z ;;
      #assert p.(verify) h a e' z' ;;
      #assert (e != e') ;;
      @ret 'bool true
    }
  ].

Definition Special_Soundness p b :=
  if b then Special_Soundness_t p else Special_Soundness_f p.

End Scheme.
