Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Program.Basics.
Import ListNotations.

Open Scope type_scope.  Open Scope string_scope.

Inductive matom : Set :=
| base : matom
| po : matom.
    
Definition mcat : Set := list matom.

Definition mobjs : list mcat :=
  [ [ base ] ; [ po ] ].

Definition mobj : mcat -> Prop := fun x => In x mobjs.

Lemma mobj_base:
  mobj [ base ].
Proof.
  cbv.
  auto.
Qed.

Lemma mobj_po:
  mobj [ po ].
Proof.
  cbv.
  auto.
Qed.

Definition mpair := (mcat * mcat).

Definition mmap (mp : mpair) : Prop :=
  match mp with
  | (x, y) => mobj x /\ mobj y
  end.

Definition mgraph := list (mcat * mcat).

Definition lmgraph (mg : mgraph) := Forall mmap mg.

Lemma nil_lmgraph:
  lmgraph nil.
Proof.
  cbv.
  auto.
Qed.

Section Mgraph.

  Variable G : mgraph.
  
  Inductive lem : mcat -> mcat -> Prop :=
  | defm : forall x y, lmgraph G -> mobj x -> mobj y -> In (x, y) G -> lem x y
  | reflm : forall x y, lmgraph G -> mobj x -> mobj y -> x = y -> lem x y
  | transm : forall x y z, lmgraph G -> mobj x -> mobj y -> mobj z -> lem x y -> lem y z -> lem x z.

End Mgraph.

Definition lemm := lem nil.

Definition mcondition := fun y : mcat => (flip lemm) y.

Axiom lem_antisym : forall x y : mcat, lem x y -> lem y x -> x = y.

Inductive lexeme : Set :=
| ÑENE : lexeme (* big *)
| GIITA : lexeme. (* small *)

Inductive fclass : Set :=
| adjc
| ñenec
| giitac
| anyc.

Definition cgraph : list (fclass * fclass) :=
[ (ñenec, adjc) ; (giitac, adjc) ; (adjc, anyc) ].
                                              
Inductive lec : fclass -> fclass -> Prop :=
| lec_def : forall x y : fclass, In (x, y) cgraph -> lec x y
| lec_refl : forall x y : fclass, x = y -> lec x y
| lec_trans : forall x y z : fclass, lec x y -> lec y z -> lec x z.

Definition mform := string.
  
Definition suffix_pa (stem:mform) : mform :=
  stem ++ "po".

Definition mtrip := mcat * mform * lexeme.

Axiom Fentry : mtrip -> Prop.

Definition ñene_base := ([ base ], "ñene", ÑENE) : mtrip.

Definition giita_base := ([ base ], "giita", GIITA) : mtrip.

Axiom f_ñene_base : Fentry ñene_base.

Axiom f_giita_base : Fentry giita_base.

Axiom base_lem_bostem : lem [ base ] [ bostem ].
Axiom ke_base_lem_bostem : lem [ ke ; base ] [ bostem ].
Axiom bostem_lem_pastem : lem [ bostem ] [ pastem ].
Axiom bo_lem_pastem : lem [ bo ; base ] [ pastem ].
Axiom bo_ke_lem_pastem : lem [ bo ; ke ; base ] [ pastem ].

Axiom add_ke : forall
    (mt : mtrip), (Fentry mt) ->
                  (lem (fst (fst mt)) [ base ]) ->
                  Fentry (cons ke (fst (fst mt)),
                          suffix_ke (snd (fst mt)),
                          (snd mt)).

Axiom add_kuna : forall
    (mt : mtrip), (Fentry mt) ->
                  (lem (fst (fst mt)) [ bostem ]) ->
                  Fentry (cons bo (fst (fst mt)),
                          suffix_bo (snd (fst mt)),
                          (snd mt)).

Axiom add_plta : forall
    (mt : mtrip), (Fentry mt) ->
                  (lem (fst (fst mt)) [ pastem ]) ->
                  Fentry (cons pa (fst (fst mt)),
                          suffix_pa (snd (fst mt)),
                          (snd mt)).

Inductive syncat : Set :=
| V_fut_1 : syncat
| V_fut_3 : syncat
| V_fut_part : syncat
| V_fut_part_aux_1 : syncat
| V_fut_part_aux_3 : syncat.

Axiom Sentry : syncat -> Prop.

Axiom ke_base_to_v_fut_part : forall
    (mt : mtrip), (Fentry mt) ->
                  (lem (fst (fst mt)) [ ke ; base ]) -> Sentry V_fut_part.

Axiom kepa_to_v_fut_part_aux_3 : forall
    (mt : mtrip), (Fentry mt) ->
                  (lem (fst (fst mt)) [ pa ; base ]) ->
                  Sentry V_fut_part_aux_3.

Axiom kepa_to_v_fut_part_aux_1 : forall
    (mt : mtrip), (Fentry mt) ->
                  (lem (fst (fst mt)) [ pa ; bo ; base ]) ->
                  Sentry V_fut_part_aux_1.

Axiom pa_ke_to_v_fut_3 : forall
    (mt : mtrip), (Fentry mt) ->
                  (lem (fst (fst mt)) [ pa ; ke ; base ]) ->
                  Sentry V_fut_3.

Axiom pa_bo_ke_to_v_fut_1 : forall
    (mt : mtrip), (Fentry mt) ->
                  (lem (fst (fst mt)) [ pa ; bo ; ke ; base ]) ->
                  Sentry V_fut_1.
