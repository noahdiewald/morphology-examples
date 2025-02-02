(** * Wao Tededo Fragment for Dissertation

This file provides a morphological fragment of Wao Terero patterns
using a version of my theoretical framework as it was defined at the
time of my dissertation. *)

(** The quasi phonemic representation of morphological forms use the
string definition from the standard library. *)

Require Import Coq.Strings.String.

(** I use unicode in this file. *)

Require Import Coq.Unicode.Utf8.

(* A portion of Needle's hyperintentional semantics *)

Load Semantics.

(** I use lists as a convenient data structure. *)

Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.

Open Scope type_scope.
Open Scope string_scope.

(** `m` are basic symbols used as components of morphological
categories. Types, functions and relations that manipulate `m` and
lists of `m` will have ₘ in their name. The comments beside the `m`
constructors below are not intended to "define" the catagories, but to
provide some intuition about which meanings and forms the element is
commonly associated with. *)

Inductive m : Set :=
| A₁ₘ (* The stem of the noun 'plant'. *)
| A₂ₘ (* The stem of the noun 'to see'. *)
| Ãₘ (* The stem of the verb 'to say'. *)
| Adoₘ (* The stem of 'same' and the numeral 'one'. *)
| Daaₘ (* The stem of 'thorn'. *)
| Diₘ (* The bound stem of the noun 'stone'. *)
| Dãtaₘ (* The stem of the verb 'to ache'. *)
| Eₘ (* The water stem. *)
| Keₘ (* The stem of the verb 'to do'. *)
| Kẽ₁ₘ (* The stem of the verb 'to eat' or 'to cut'. *)
| Kẽ₂ₘ (* The stem of the manioc noun. *)
| Okiyeₘ (* The stem for 'woman'. *)
| Peẽₘ (* The bound stem for the noun 'plantain'. *)
| Teₘ (* The bound stem for 'chonta' and 'chicha'. *)
| Wiₘ (* The bound stem of the noun 'canoe'. *)
| Yẽdẽₘ (* The stem of the adjective 'big'. *)
(* Lexical suffixes *)
| bõ₁ₘ (* The 'seed' lexical suffix. *)
| dẽₘ (* The 'food' lexical suffix. *)
| ka₁ₘ (* The 'fruit' lexical suffix. *)
| kã₁ₘ (* The 'body' lexical suffix. *)
| pa₁ₘ (* The 'board' lexical suffix. *)
| poₘ (* The 'hand' lexical suffix. *)
| pẽₘ (* The 'liquid' lexical suffix. *)
| ta₁ₘ (* The 'shell' lexical suffix. *)
| wẽₘ (* The 'plant' lexical suffix. *)
(* Tense affixes *)
| ke₁ₘ (* The future tense suffix. *)
| ta₂ₘ (* The past tense suffix. *)
(* Person and number affixes *)
| biₘ (* The second person singular suffix. *)
| bĩₘ (* The non-singular second person suffix. *)
| boₘ (* The first person singular suffix. *)
| bõ₂ₘ (* The non-singular first person suffix. *)
| daₘ (* The dual suffix. *)
| dãₘ (* The feminen suffix. *)
| diₘ (* The plural person suffix. *)
| kã₂ₘ (* The third person sentient suffix. *)
(* Final verbal inflection *)
| pa₂ₘ (* The declarative suffix. *)
| teₘ (* The gerundive suffix. *)
(* Final nominal inflection. *)
| ke₂ₘ (* The limitive suffix. *)
| ka₂ₘ (* The instrumental suffix. *)
(* Abstract m categories. *)
| LSₘ (* Ending in a lexical suffix. *)
| PERSONₘ (* Ending in a person suffix. *)
| PERSONABLEₘ (* Ending in a person suffix. *)
| ROOTₘ (* A singleton. *)
| INFₘ (* A stem for inflection. *)
| LSABLEₘ (* A stem for lexical suffixes. *)
| NONFIRSTₘ (* Not a first person stem. *)
| NUMBERABLEₘ (* A stem for number suffixes. *)
| DUALABLEₘ (* A stem for the dual. *)
| PLURALABLEₘ (* A stem for the plural suffix. *)
(* For instances when a meaningless m is needed. *)
| noneₘ.

(** Below I define boolean equality of `m`. The `+` is the disjoint
sum constructor. Both equality (`=`) and inequality (`≠`) of `m` are
of type Prop, for instance, LSₘ = LSₘ : Prop. Within constructive
logic, it is not automatically the case that proving that something is
equal proves the negation of inequality, as it does in classical
logic. It can be useful to have this property for some types. For
simple inductive types like `m`, it is not difficult to provide a
conversion from proofs of equality to boolean values. Bools are in the
universe of Set and behave according the classical rules of boolean
logic. The first step to doing the conversion is declaring a type
`m_dec`, which takes two `m` and returns a disjoint sum type. The sum
type in Coq, used here, is called `sumbool`, and takes two Prop
arguments. It is defined inductively, such that `inleft (_:A)` or
`inright (_:B)`, where A and B are the two Prop arguments. So, a proof
of A results in the construction of the type using `inleft`. Note that
curly braces are used around the (in)equalities. This means that these
are implicit arguments. Their witnesses may be inferred from the
definition of the inductive type `m`. For this reason, a proof of
`m_dec` may be supplied directly with the `decide equality`
tactic. The result of this is to say, that `m` may be equal or not
equal but not both. They will always be one or the other. The `if _
then _ else _` function is defined such that the first clause is
returned on `inleft`, while the second, "else" clause is returned on
`inright`. This provides the conversion to boolean values. The result
is that functions that utilize boolean equality are now compatible
with `m`. *)

Definition m_dec : ∀ α β : m, {α = β} + {α ≠ β}.
Proof. decide equality. Defined.
Definition eqₘ α β := if m_dec α β then true else false.

Example eq_kaₘ : eqₘ ka₁ₘ ka₁ₘ = true.
Proof. compute. reflexivity. Qed.

(** Using lists of `m` instances, category names `Mₘ` are
licensed. The reason for doing this is that not all permutations of
all sublists of `m` correspond to grammatical categories of form
paradigm entries. The lists and `m` are important in constructing form
categories but the constructor for a grammatical form category is
Mₘ. *)

Axiom Mₘ : (list m) → Prop.

(** According to convention, which may depend on the needs of a
particular analysis or the preferred style of the theorist, some `m`
are only indirectly associated with morphological process lists, and
only occur as singletons. I call the `m` that correspond to particular
morphological processes "concrete". Other categories are used to
provide super categories for these categories. I call these categories
"abstract" categories and it is usefult to be able to refer to a list
of them.

They come in two flavors. One describes how a stem is, such as LSₘ,
used when the stem ends in a LS. The other describes its potential for
further affixation, such as LSABLEₘ, a stem that may be affixed with
an LS. *)

Definition abstractsₘ : list m :=
  [ LSₘ ; (* Ends in a LS. *)
    PERSONₘ ; (* Ends in person affix. *)
    PERSONABLEₘ ; (* May be affixed for person. *)
    ROOTₘ ; (* Singleton. *)
    INFₘ ; (* Inflected. *)
    LSABLEₘ ; (* May be affixed with LS. *)
    NONFIRSTₘ ; (* Ends in a non-first person. *)
    NUMBERABLEₘ ; (* May take the dual or plural. *)
    DUALABLEₘ ; (* May take the dual. *)
    PLURALABLEₘ (* May take the plural. *)
  ].

(** There are other `m` that are usefully grouped to make the rules
that define the partial order on `Mₘ` more succinct. *)

(** `lssₘ` is a list of lexical suffixes. Items are described in the
comments on the definition of `m'. *)

Definition lssₘ : list m :=
  [ bõ₁ₘ ;
    dẽₘ ;
    ka₁ₘ ;
    kã₁ₘ ;
    pa₁ₘ ;
    poₘ ;
    pẽₘ ;
    ta₁ₘ ;
    wẽₘ
  ].

(** `nonfirstsₘ` are affixes used for non-first person and number
marking. *)

Definition nonfirstsₘ : list m :=
  [ biₘ ;
    bĩₘ ;
    daₘ ;
    dãₘ ;
    diₘ ;
    kã₂ₘ
  ].

(** `personsₘ` are all person marking. *)

Definition personsₘ : list m := boₘ :: bõ₂ₘ :: nonfirstsₘ.

(** Classes of roots that may be useful to refer to. *)

Definition onerootsₘ : list m := [ Adoₘ ].

Definition verbrootsₘ : list m := [ A₂ₘ ; Ãₘ ; Keₘ ].

Definition verblsrootssₘ : list m := [ Dãtaₘ ; Kẽ₁ₘ ].

Definition adjrootsₘ : list m := [ Yẽdẽₘ ].

Definition inanimrootsₘ : list m := [ A₁ₘ ; Daaₘ ; Diₘ ; Eₘ ; Kẽ₂ₘ ; Peẽₘ ; Teₘ ; Wiₘ ].

Definition animrootsₘ : list m := [ Okiyeₘ ].
           
(** K are names of form classes, similar in concept to inflection
classes. The uppercase kappa `K' is a mnemonic for /klæs/. Like ₘ the
ₖ subscript is used for names of types, functions and relations
associated with K. Variables of type K are written as κ or κₙ. The
noneₖ class is for the nil case of a list of categories. It has no
theoretical meaning. It is used so that the klass function below can
be defined as a total function, rather than using Maybe/option. *)

Inductive K : Set :=
| adjₖ (* Adjective-like items have person marking and lexical
  suffixes in competition. *)
| animₖ (* Animate noun-like items have person marking but no lexical
  suffixes. *)
| awẽₖ (* The noun awẽ ends in -wẽ, only. *)
| bodyₖ (* Some items take only body-part affixes. *)
| dikaₖ (* The noun dika ends in -ka, only. *)
| epẽₖ (* The noun epẽ ends in -pẽ, only. *)
| inanimₖ (* Inanimate noun-like items may have more than one LS, but
  no person marking. *)
| kẽdẽₖ (* The stem for manioc has a -we, and -dẽ ending but nothing
  else. *)
| oneₖ (* The class of adoke, `one', and ado, `same'. *)
| personₖ (* Items that take person marking. *)
| peẽdẽₖ (* The noun peẽdẽ ends only in -dẽ. *)
| singlelsₖ (* This covers adjectives and LS taking verbs. *)
| tepẽₖ (* The noun tepẽ and tewẽ, which have only two endings. *)
| thingₖ (* Items that take any LS. *)
| verbbodyₖ (* Verbs that take only body LSs *)
| verblsₖ (* Verbs that take LSs. *)
| verbₖ (* General verbs, which may not take LSs. *)
| wipoₖ (* The noun wipo ends only in -po. *)
| noneₖ. (* The default class. *)

Definition K_dec : ∀ α β : K, {α = β} + {α ≠ β}.
Proof. decide equality. Defined.
Definition eqₖ α β := if K_dec α β then true else false.

Example eq_eatyₖ : eqₖ bodyₖ bodyₖ = true.
Proof. compute. reflexivity. Qed.

(* Below is the list of rules for the form class order. Items on the
left of the pairs are ordered below those on the right. These rules
are refered to in the definition of the ≤ₖ order. *)

Definition le_rulesₖ : list (K * K) :=
  [ (bodyₖ, dikaₖ) ; (* Items with the LS -ka may be body part LSs. *)
    (bodyₖ, wipoₖ) ; (* Items with the LS -po may be body part LSs. *)
    (tepẽₖ, epẽₖ) ; (* The te- stem may end in -pẽ. *)
    (tepẽₖ, awẽₖ) ; (* The te- stem may end in -wẽ. *) 
    (kẽdẽₖ, peẽdẽₖ) ; (* The kẽ- stem may end in -dẽ. *) 
    (kẽdẽₖ, awẽₖ) ; (* The kẽ- stem may end in -wẽ. *) 
    (thingₖ, kẽdẽₖ) ; (* The general ls-taking class includes -wẽ and
    -dẽ *)
    (thingₖ, tepẽₖ) ; (* The general ls-taking class includes -wẽ and
    -pẽ *)
    (thingₖ, bodyₖ) ; (* The general ls-taking class includes body
    affixes *)
    (animₖ, personₖ) ; (* Animate nouns may take person marking *)
    (adjₖ, personₖ) ; (* Adjectives may take person marking *)
    (verbₖ, personₖ) ; (* Verbs may take person marking *)
    (oneₖ, personₖ) ; (* The numeral one may take person marking *)
    (verblsₖ, verbₖ) ; (* Verbs that take lexical suffixes are verbs
    *)
    (verbbodyₖ, verblsₖ) ; (* Verbs that take body LS only are LS
    taking verbs *)
    (verbbodyₖ, bodyₖ) ; (* Verbs that take body LS *)
    (adjₖ, thingₖ) ; (* Adjectives can take any lexical suffix *)
    (oneₖ, thingₖ) ; (* The numeral one may take any lexical suffix *)
    (inanimₖ, thingₖ) ; (* Inanimate nominals may take any lexical
    suffix *)
    (verblsₖ, singlelsₖ) ; (* Verbs only take one LS *)
    (adjₖ, singlelsₖ) (* Adjectives only take one LS *)
  ].

Fixpoint inrulesₖ (α : K) (β : K) (l : list (K * K)) : bool :=
  match l with
  | [] => false
  | (x, y) :: t =>
      match (eqₖ α x), (eqₖ β y) with
      | true, true => true
      | _, _ => inrulesₖ α β t
      end
  end.

(** Form classes are ordered. *)
    
Inductive leₖ : K → K → Prop :=
| reflₖ : ∀ α, leₖ α α
| transₖ : ∀ α β γ, leₖ α β → leₖ β γ → leₖ α γ
| rulesₖ : ∀ α β, inrulesₖ α β le_rulesₖ = true → leₖ α β.

Axiom antisymₖ : ∀ α β, leₖ α β → leₖ β α → α = β.

Infix "≤ₖ" := leₖ (at level 60, right associativity).

Example adjₖ_leq_thingₖ : adjₖ ≤ₖ thingₖ.
Proof.
  apply rulesₖ.
  simpl.
  reflexivity.
Qed.

(** A subset of `list m` terms are stems.
They may not be free so they may not correspond to a Mₘ. *)

Fixpoint klass (α : list m) : K :=
  match α with
  | [] => noneₖ
  | [Adoₘ] => oneₖ
  | [A₁ₘ] => awẽₖ
  | [A₂ₘ] => verbₖ
  | [Ãₘ] => verbₖ
  | [Daaₘ] => inanimₖ
  | [Diₘ] => dikaₖ
  | [Dãtaₘ] => verbbodyₖ
  | [Eₘ] => epẽₖ
  | [Keₘ] => verbₖ
  | [Kẽ₁ₘ] => verbbodyₖ
  | [Kẽ₂ₘ] => kẽdẽₖ
  | [Okiyeₘ] => animₖ
  | [Peẽₘ] => peẽdẽₖ
  | [Teₘ] => tepẽₖ
  | [Wiₘ] => wipoₖ
  | [Yẽdẽₘ] => adjₖ
  | [_ ; A₁ₘ] => inanimₖ
  | [_ ; Diₘ] => inanimₖ
  | [_ ; Eₘ] => inanimₖ
  | [_ ; Kẽ₂ₘ] => inanimₖ
  | [_ ; Peẽₘ] => inanimₖ
  | [_ ; Teₘ] => inanimₖ
  | [_ ; Wiₘ] => inanimₖ
  | _ :: t => klass t
  end.

Example yẽdẽka_klass : klass [ka₁ₘ ; Yẽdẽₘ] = adjₖ.
Proof. compute. reflexivity. Qed.

(** These are some helper predicates for determining super categories of Mₘ *)

Fixpoint inₘ (α : m) (l : list m) : bool :=
  match l with
  | [] => false
  | x :: t => if eqₘ x α then true else inₘ α t
  end.

Fixpoint inabbₘ (α : m) (β : m) (l : list (list m * list m)) : bool :=
      match l with
      | [] => false
      | ([x], [y]) :: t =>
          match (eqₘ α x), (eqₘ β y) with
          | true, true => true
          | _, _ => inabbₘ α β t
          end
      | _ :: t => inabbₘ α β t
      end.

(** Relationships between abstract Mₘ, which may be shared by all form classes. *)

Definition abstract_leₘ_rulesₘ : (list (list m * list m)) :=
  [ ([ ROOTₘ ],[ PERSONABLEₘ ]) ;
    ([ ROOTₘ ], [ DUALABLEₘ ]) ; (* Although not all roots take person
    affixes, most do and those that don't will be of the wrong form
    class for this ordering to matter. *)
    ([ NUMBERABLEₘ ], [ DUALABLEₘ]) ;
    ([ NUMBERABLEₘ ], [ PLURALABLEₘ ])
  ].

Definition inabₘ (α : list m) (β : list m) : bool :=
    match α, β with
    | [], _ => false
    | _, [] => false
    | _ :: _ :: _, _ => false
    | _, _ :: _ :: _ => false
    | [x], [y] => inabbₘ x y abstract_leₘ_rulesₘ
    end.

Definition hdIn (l₁ : list m) (l₂ : list m) : bool :=
  match l₁ with
  | [] => false
  | x :: _ => inₘ x l₂
  end.

Definition isNonFirstₘ (l₁ : list m) : bool :=
  match l₁ with
  | [] => false
  | [x] => false
  | x :: y :: _ => andb (inₘ x nonfirstsₘ) (negb (eqₘ y bõ₂ₘ))
  end.

(** All singeltons of abstract `m` are Mₘ *)

Axiom Mₘ_abstractsₘ : ∀ (α : m), inₘ α abstractsₘ = true → Mₘ [α].

(** A partial order is defined over `m` lists, where only `Mₘ`
instances are ordered. The basic properties are defined in the
inductive type and a following axiom of antisymetry. The meat of the
definition are more specific constructors that define the language
specific category order. *)

Inductive leₘ : (list m) → (list m) → Prop :=
| reflₘ : ∀ α, Mₘ α → leₘ α α
| transₘ : ∀ α β γ, Mₘ α → Mₘ β → Mₘ γ → leₘ α β → leₘ β γ → leₘ α γ
(* All non-abstract singleton Mₘ are ≤ₘ [ ROOTₘ ]. *)
| rootₘ : ∀ α, Mₘ α → length α = 1 → ~ hdIn α abstractsₘ = true → leₘ α [ROOTₘ]
(* When the last process was a lexical suffix process, the category is
a subcategory of Mₘ [LSₘ]. *)
| lsₘ : ∀ α, Mₘ α → hdIn α lssₘ = true → leₘ α [LSₘ]
(* When the last `m` corresponds to person marking, the category is a
subcategory of Mₘ [PERSONₘ]. *)
| prₘ : ∀ α, Mₘ α → hdIn α personsₘ = true → leₘ α [PERSONₘ]
(* bõ₂ₘ and bĩₘ correspond to stem endings where person number affixes
may be added. Note, either plural or dual may be added to such
stems. Only plural may be added to a stem with dãₘ. See below. *)
| numerableₘ : ∀ α, Mₘ α → hdIn α [bõ₂ₘ;bĩₘ] = true → leₘ α [NUMBERABLEₘ]
(* The placement of the past tense morph depends on whether or not the
person marking on a verb is first person or otherwise. *)
| nirstyₘ : ∀ α, Mₘ α → isNonFirstₘ α = true → leₘ α [NONFIRSTₘ]
(* The affix dãₘ may be followed by plural marking. *)
| dãplₘ : ∀ α, Mₘ α → hdIn α [dãₘ] = true → leₘ α [PLURALABLEₘ]
(* The relation between abstract Mₘ is listed separately. *)
| abstract_leₘ : ∀ α β, inabₘ α β = true → leₘ α β
(* The Mₘ, which describe morphotactics are parameterized based on class. *)
(* Some verbs, demonstratives, and adjectives allow a single LS *)    
| singleₘ : ∀ α, Mₘ α → klass α ≤ₖ singlelsₖ → leₘ [ROOTₘ] [LSABLEₘ]
(* LSs and person marking don't compete on verbs. *)
| verblsₘ : ∀ α, Mₘ α → klass α ≤ₖ verblsₖ → leₘ [LSₘ] [PERSONABLEₘ]
(* Inanimate nouns may take any number of LS *)
| inanimₘ : ∀ α, Mₘ α → klass α ≤ₖ inanimₖ → leₘ [LSₘ] [LSABLEₘ].
                                                 
Axiom antisymₘ : ∀ α β : (list m), leₘ α β → leₘ β α → α = β.

Infix "≤ₘ" := leₘ (at level 60, right associativity).

Example leq_is_refl : [LSₘ] ≤ₘ [LSₘ].
Proof.
  apply reflₘ.
  apply Mₘ_abstractsₘ.
  simpl.
  reflexivity.
Qed.

(** Rather than eagerly building up strings, morphological rules build
a list of processes that are applied at some point of evaluation, such
as evaluating string equality.  The `applyₚᵣ' function applies all of
the processes in order to the empty string. Processes and process
related functions have a ₚᵣ subscript. *)

Definition processₚᵣ := (string → string) → (string → string).

Fixpoint applyₚᵣ (processes : list processₚᵣ) (acc : string → string) : string :=
  match processes, acc with
  | nil, acc' => acc' ""
  | p :: ps, acc' => applyₚᵣ ps (p acc')
  end.

(** Processes are not string to string functions but functions from
string to string functions to string to string functions. Stems,
notably, take an input string to string function and return a
constant-like function, which disgards its input. *)

Definition toₚᵣ (p : string → string) : (string → string) :=
  λ (s : string), (p s) ++ "to".

Definition ãₚᵣ (p : string → string) : (string → string) :=
  λ (_ : string), p "ã".

Definition di₁ₚᵣ (p : string → string) : (string → string) :=
  λ (_ : string), p "di".

Definition yẽdẽₚᵣ (p : string → string) : (string → string) :=
  λ (_ : string), p "yẽdẽ".

Definition kẽₚᵣ (p : string → string) : (string → string) :=
  λ (_ : string), p "kẽ".

Definition keₚᵣ (p : string → string) : (string → string) :=
  λ (_ : string), p "ke".

Definition peẽₚᵣ (p : string → string) : (string → string) :=
  λ (_ : string), p "peẽ".

Definition kaₚᵣ (p : string → string) : (string → string) :=
  λ (stem : string), p (stem ++ "ka").

Definition wẽₚᵣ (p : string → string) : (string → string) :=
  λ (stem : string), p (stem ++ "wẽ").

Definition dẽₚᵣ (p : string → string) : (string → string) :=
  λ (stem : string), p (stem ++ "dẽ").

Definition paₚᵣ (p : string → string) : (string → string) :=
  λ (stem : string), p (stem ++ "pa").

Definition boₚᵣ (p : string → string) : (string → string) :=
  λ (stem : string), p (stem ++ "bo").

Definition bõₚᵣ (p : string → string) : (string → string) :=
  λ (stem : string), p (stem ++ "bõ").

Definition biₚᵣ (p : string → string) : (string → string) :=
  λ (stem : string), p (stem ++ "bi").

Definition bĩₚᵣ (p : string → string) : (string → string) :=
  λ (stem : string), p (stem ++ "bĩ").

Definition kãₚᵣ (p : string → string) : (string → string) :=
  λ (stem : string), p (stem ++ "kã").

Definition daₚᵣ (p : string → string) : (string → string) :=
  λ (stem : string), p (stem ++ "da").

Definition dãₚᵣ (p : string → string) : (string → string) :=
  λ (stem : string), p (stem ++ "dã").

Definition di₂ₚᵣ (p : string → string) : (string → string) :=
  λ (stem : string), p (stem ++ "di").

Definition taₚᵣ (p : string → string) : (string → string) :=
  λ (stem : string), p (stem ++ "ta").

(** The `idₚᵣ' function is used as input the result of applying
processes. *)

Definition idₚᵣ (s : string) : string := s.

(** The example below demonstrates how processes result in a string *)

Example yẽdẽwẽ_application:
  applyₚᵣ (wẽₚᵣ :: yẽdẽₚᵣ :: nil) idₚᵣ = "yẽdẽwẽ".
Proof.
  simpl.
  reflexivity.
Qed.

(** This example demonstrates a process that is always applied last *)

Example bõdito_application:
  applyₚᵣ (toₚᵣ :: di₂ₚᵣ :: bõₚᵣ :: nil) idₚᵣ = "bõdito".
Proof.
  simpl.
  reflexivity.
Qed.

(** The data structure used by the form paradigm is a pair of a
category (list m) and a list of processes. *)

Definition structₘₚ := (list m * list processₚᵣ).

Fixpoint intersectionₘ (α β : list m) : bool :=
  match α with
  | [] => false
  | x :: t => match inₘ x β with
              | true => true
              | false => intersectionₘ t β
              end
  end.

Definition combineₘₚ (newₘ prevₘ : list m) (newₚᵣ prevₚᵣ : list processₚᵣ) : structₘₚ :=
  match newₘ with
  | [] => (prevₘ, prevₚᵣ)
  | _ => match intersectionₘ newₘ prevₘ with
         | true => (prevₘ, prevₚᵣ)
         | false => (app newₘ prevₘ, app newₚᵣ prevₚᵣ)
         end
  end.

(** A form to form mapping rule has the following structure.  There is
an input compound category, a form class constraint, a new category
that will be added to the compound category and a new process to be
added to the process list. *)

(* The first rule schema for defining a form-form mapping is
rule1ₘₚ. This rule takes the category that the rules will be
constrained by, the class it will be constrained by, some new category
information and new process information. It provides a function that
takes an input form entry struct, and proofs that the entry matches
the category and class conditions. It then returns a new entry where
the new category and process information is appended to the existing
information. *)

Definition rule1ₘₚ (catₘ : list m) (κ : K) (newₘ : list m) (newₚᵣ : list processₚᵣ) :=
  λ (α : structₘₚ)
    (proofₘ : fst α ≤ₘ catₘ)
    (proofₖ : klass (fst α) ≤ₖ κ),
    combineₘₚ newₘ (fst α) newₚᵣ (snd α).

(* The rule2ₘₚ schema is essentially the same as rule1ₘₚ, except that
combineₘₚ takes the tails of the input category and process
information, roughly swapping out the heads. This is why these rules
are called lateral rules. *)

Definition rule2ₘₚ (catₘ : list m) (κ : K) (newₘ : list m) (newₚᵣ : list processₚᵣ) :=
  λ (α : structₘₚ)
    (proofₘ : fst α ≤ₘ catₘ)
    (proofₖ : klass (fst α) ≤ₖ κ),
    combineₘₚ newₘ (tail (fst α)) newₚᵣ (tail (snd α)).

(* The inductive definition of valid form entries. *)

Inductive FEₘₚ : structₘₚ → Prop :=
| kẽMP : FEₘₚ ( [Kẽ₁ₘ], [kẽₚᵣ] )
| keMP : FEₘₚ ( [Keₘ], [keₚᵣ] )
| yẽdẽMP : FEₘₚ ( [Yẽdẽₘ], [yẽdẽₚᵣ] )
| dikaMP : FEₘₚ ( [ka₁ₘ ; Diₘ], [kaₚᵣ ; di₁ₚᵣ] )
| peẽdẽMP : FEₘₚ ( [dẽₘ ; Peẽₘ], [dẽₚᵣ ; peẽₚᵣ] )
| ãMP : FEₘₚ ( [Ãₘ], [ãₚᵣ] )
| kaMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [LSABLEₘ] dikaₖ [ka₁ₘ] [kaₚᵣ])
                     α proofₘ proofₖ)
| wẽMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [LSABLEₘ] awẽₖ [wẽₘ] [wẽₚᵣ])
                     α proofₘ proofₖ)
| dẽMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [LSABLEₘ] peẽdẽₖ [dẽₘ] [dẽₚᵣ])
                     α proofₘ proofₖ)
| kã₁MP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [LSABLEₘ] bodyₖ [kã₁ₘ] [kãₚᵣ])
                     α proofₘ proofₖ)
| kã₂MP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [PERSONABLEₘ] personₖ [kã₂ₘ] [kãₚᵣ])
                     α proofₘ proofₖ)
| boMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [PERSONABLEₘ] personₖ [boₘ] [boₚᵣ])
                     α proofₘ proofₖ)
| bõ₂MP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [PERSONABLEₘ] personₖ [bõ₂ₘ] [bõₚᵣ])
                     α proofₘ proofₖ)
| biMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [PERSONABLEₘ] personₖ [biₘ] [biₚᵣ])
                     α proofₘ proofₖ)
| bĩMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [PERSONABLEₘ] personₖ [bĩₘ] [bĩₚᵣ])
                     α proofₘ proofₖ)
| daMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [DUALABLEₘ] personₖ [daₘ] [daₚᵣ])
                     α proofₘ proofₖ)
| dãMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [PERSONABLEₘ] personₖ [dãₘ] [dãₚᵣ])
                     α proofₘ proofₖ)
| diMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [PLURALABLEₘ] personₖ [diₘ] [di₂ₚᵣ])
                     α proofₘ proofₖ)
| paMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [INFₘ] verbₖ [pa₂ₘ] [paₚᵣ])
                     α proofₘ proofₖ)
| tapaMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [NONFIRSTₘ] verbₖ [pa₂ₘ ; ta₂ₘ] [paₚᵣ ; taₚᵣ])
                     α proofₘ proofₖ)
| tabõMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [PERSONABLEₘ] verbₖ [bõ₂ₘ ; ta₂ₘ] [bõₚᵣ ; taₚᵣ])
                     α proofₘ proofₖ)
| taboMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [PERSONABLEₘ] verbₖ [boₘ ; ta₂ₘ] [boₚᵣ ; taₚᵣ])
                     α proofₘ proofₖ).

Example Kẽ₁ₘ_is_FE : FEₘₚ ( [Kẽ₁ₘ], [kẽₚᵣ] ).
apply kẽMP.
Qed.

(** Anything that is the category of a proveable form paradigm member
has a validly named compound category. *)

Axiom Mₘ_are_FE_fst : ∀ (cat : list m) (α : structₘₚ), FEₘₚ α → cat = fst α → Mₘ cat.

Example Kẽ₁ₘ_is_Mₘ : Mₘ [Kẽ₁ₘ].
Proof.
  assert (equal_to_first : ([Kẽ₁ₘ] = fst ([Kẽ₁ₘ], [kẽₚᵣ]))).
  simpl.
  reflexivity.
  apply (Mₘ_are_FE_fst [Kẽ₁ₘ] ( [Kẽ₁ₘ], [kẽₚᵣ] ) Kẽ₁ₘ_is_FE equal_to_first).
Qed.
  
(** Form paradigm string equivalence states that when two structures
that have process lists that reduce to the same string, they are
equivalent, so long as their compound categories are valid names.  It
may be that the string is produced by distinct process lists or that
the compound category is different.  The str_equivₘₚ constructor
states that they are never the less equivalent, equal strings are the
determining factor. If two structures are equivalent, compound
categories may be swapped. *)

Inductive equivₘₚ : structₘₚ → structₘₚ → Prop :=
| reflₘₚ : ∀ α : structₘₚ, Mₘ (fst α) → equivₘₚ α α
| symₘₚ : ∀ α β : structₘₚ, Mₘ (fst α) → Mₘ (fst β) → equivₘₚ α β → equivₘₚ β α
| transₘₚ : ∀ α β γ, Mₘ (fst α) → Mₘ (fst β) → Mₘ (fst γ) → equivₘₚ α β → equivₘₚ β γ → equivₘₚ α γ
| str_equivₘₚ : ∀ α β : structₘₚ, Mₘ (fst α) → Mₘ (fst β) → applyₚᵣ (snd α) = applyₚᵣ (snd β) → equivₘₚ α β.

Infix "≡ₘₚ" := equivₘₚ (at level 90).

(** The form paradigm for some lexeme is an equivalence class *)

(* Inductive Pₘₚ : mpₘₚ → mpₘₚ → Prop := *)
(* | inₘₚ : ∀ α β l, MPₘₚ α l → MPₘₚ β l → Pₘₚ α β *)
(* | reflₘₚ : ∀ α l, MPₘₚ α l → Pₘₚ α α *)
(* | transₘₚ : ∀ α β γ, Pₘₚ α β → Pₘₚ β γ → Pₘₚ α γ *)
(* | symₘₚ : ∀ α β, Pₘₚ α β → Pₘₚ β α. *)

(** Below is a highly simplified phenogrammatical type for LCG. *)

Inductive ϕ : Set :=
| ε
| η : string → ϕ
| concatϕ (α β : ϕ).

Infix "•" := concatϕ (at level 60, right associativity).

(** Below is a highly simplified tectogrammatical type for LCG. *)

Inductive τ : Set :=
| NP
| N
| Fin
| infτ (α β : τ).

(** Below is a portion of Jordan Needle's formalization of Agnostic
Hyper-intentional Semantics. Much of what makes the theory agnostic
and hyper-intentional is not provided here. The goal is simply to
embed the terms of the semantic theory below a single type. The idea
is to provide an encoding of the types of the many types of the
semantic theory under an inductive type stat_term, which is a single
type within Set. The `ent`, `prp` and `func` constructors are simple
terms of type stat_term and may not have inhabitants. Sns is a
recursive function that returns a type within Set given a stat_term
encoding. The stat_term is basically just a syntactic expression of
the types of the semantic logic. Sns converts that syntactic
representation into acutal types. *)

(** A number of types for meanings. *)

Axiom big : (e → prop) → e → prop.

Axiom tall : (e → prop) → e → prop.

Axiom head : e → prop.

Axiom rock : e → prop.

Axiom fruit : e → prop.

Axiom thorn : e → prop.

Axiom plant : e → prop.

Axiom pole : e → prop.

Axiom branch : e → prop.

Axiom hurt : e → e → prop.

Axiom say : e → prop → prop.

Axiom liquid : e → prop.

Axiom see : e → e → prop.

Axiom doo : e → prop → prop.

Axiom same : (e → prop) → e → prop.

Axiom cutt : e → e → prop.

Axiom eat : e → prop.

Axiom woman : e → prop.

Axiom plantain : e → prop.

Axiom chonta_palm : e → prop.

Axiom chicha : e → prop.

Axiom canoe : e → prop.

Axiom seed : e → prop.

Axiom food : e → prop.

Axiom body : e → prop.

Axiom meat : e → prop.

Axiom board : e → prop.

Axiom flat_thing : e → prop.

Axiom shell : e → prop.

Axiom paper : e → prop.

Axiom small_flat_thing : e → prop.

Axiom small_round_thing : e → prop.

Axiom round_thing : e → prop.

Axiom hand : e → prop.

Axiom cluster : e → prop.

Axiom past : e → prop.

Axiom future : e → prop.

Axiom trans : e → e → prop.

Axiom onenoun : e → prop.

Axiom to_trans : (e → prop) → (e → e → prop).

Axiom ι : (e → prop) → e.

(** `sense` is a Sigma type, a dependent sum. Σ(x:A), B(x) is the
notionation written for the constructor. So for { s : stat_term & Sns
s }, the type corresponds to Σ(s:stat_term), Sns(s). `s` is a stat
term and `Sns s` is a type "indexed" by `s`, belonging to a family of
types, in this case `e`, `prop`, and the types of functions of things
of type `e` and `prop`.

Usually, in the literature, the type is written Σ(x:A), B(x), but
given that x:A is recoverable from the type of B, the type need only
invoke the predicate, as below. *)

Definition sense := sigT Sns.

Definition adjsense := existT Sns (func (func ent prp) (func ent prp)).

Definition intranssense := existT Sns (func ent prp).

Definition transsense := existT Sns (func ent (func ent prp)).

Definition intersectls : ((e → prop) → e → prop) → (e → prop) → (e → prop) → e → prop :=
  λ adj ls n x,(adj n x) and (ls x) and (n x).

Inductive lsmeaning : (e → prop) → m → Prop :=
| bõ₁ₛfruit : ∀ m, m = bõ₁ₘ → lsmeaning fruit m
| bõ₁ₛseed : ∀ m, m = bõ₁ₘ → lsmeaning seed m
| bõ₁ₛround : ∀ m, m = bõ₁ₘ → lsmeaning round_thing m
| bõ₁ₛsmall : ∀ m, m = bõ₁ₘ → lsmeaning small_round_thing m
| ka₁ₛfruit : ∀ m, m = bõ₁ₘ → lsmeaning fruit m
| ka₁ₛseed : ∀ m, m = bõ₁ₘ → lsmeaning seed m
| ka₁ₛhead : ∀ m, m = bõ₁ₘ → lsmeaning head m
| ka₁ₛrock : ∀ m, m = bõ₁ₘ → lsmeaning rock m
| dẽₛfood : ∀ m, m = dẽₘ → lsmeaning food m
| pa₁ₛboard : ∀ m, m = pa₁ₘ → lsmeaning board m
| pa₁ₛflat : ∀ m, m = pa₁ₘ → lsmeaning flat_thing m
| poₛhand : ∀ m, m = poₘ → lsmeaning hand m
| poₛcanoe : ∀ m, m = poₘ → lsmeaning canoe m
| poₛcluster : ∀ m, m = poₘ → lsmeaning cluster m
| pẽₛliquid : ∀ m, m = pẽₘ → lsmeaning liquid m
| ta₁ₛshell : ∀ m, m = ta₁ₘ → lsmeaning shell m
| ta₁ₛpaper : ∀ m, m = ta₁ₘ → lsmeaning paper m
| wẽₛplant : ∀ m, m = wẽₘ → lsmeaning plant m
| wẽₛpole : ∀ m, m = wẽₘ → lsmeaning pole m
| wẽₛbranch : ∀ m, m = wẽₘ → lsmeaning branch m.

Inductive inmeaning : (e → prop) → list m → Prop :=
| thornₛ : ∀ cat, cat = [ Daaₘ ] → inmeaning thorn cat
| eat_intransₛ : ∀ cat, cat = [ Kẽ₁ₘ ] → inmeaning eat cat
| womanₛ : ∀ cat, cat = [ Okiyeₘ ] → inmeaning woman cat.

Inductive trmeaning : (e → e → prop) → list m → Prop :=
| hurtₛ : ∀ cat, cat = [ Dãtaₘ ] → trmeaning hurt cat
| seeₛ : ∀ cat, cat = [ A₂ₘ ] → trmeaning see cat
| cutₛ : ∀ cat, cat = [ Kẽ₁ₘ ] → trmeaning cutt cat
| eat_transₛ : ∀ cat, cat = [ Kẽ₁ₘ ] → trmeaning (to_trans eat) cat.

Inductive adjmeaning : ((e → prop) → e → prop) → list m → Prop :=
| bigₛ : ∀ cat, cat = [ Yẽdẽₘ ] → adjmeaning big cat
| tallₛ : ∀ cat, cat = [ Yẽdẽₘ ] → adjmeaning tall cat
| sameₛ : ∀ cat, cat = [ Adoₘ ] → adjmeaning same cat
| adjlsₛ : ∀ cat α β, cat ≤ₘ [ LSₘ ] → lsmeaning α (hd noneₘ cat) → adjmeaning β (tail cat) → adjmeaning (intersectls β α) cat.

Inductive emeaning : e → list m → Prop :=
| definite_adjₛ : ∀ cat (α : (e → prop) → e → prop), adjmeaning α cat → emeaning (ι (α onenoun)) cat
| definite_nounₛ : ∀ cat (α : e → prop), inmeaning α cat → emeaning (ι α) cat.

Inductive meaning : sense → list m → Prop :=
| eₛ : ∀ cat (α : e), emeaning α cat → rmeaning (existT Sns ent α) cat
| inₛ : ∀ cat (α : e → prop), inmeaning α cat → rmeaning (intranssense α) cat
| trₛ : ∀ cat (α : e → e → prop), trmeaning α cat → rmeaning (transsense α) cat
| adjₛ : ∀ cat (α : (e → prop) → e → prop), adjmeaning α cat → rmeaning (adjsense α) cat.

Example yẽdẽ_fe : FEₘₚ ([ Yẽdẽₘ ], [ yẽdẽₚᵣ ]).
Proof.
  apply yẽdẽMP.  
Qed.

Example Yẽdẽ_is_Mₘ : Mₘ [ Yẽdẽₘ ].
Proof.
  assert (equal_to_first : ([Yẽdẽₘ] = fst ([ Yẽdẽₘ ], [ yẽdẽₚᵣ ]))).
  reflexivity.
  apply (Mₘ_are_FE_fst [Yẽdẽₘ] ([ Yẽdẽₘ ], [ yẽdẽₚᵣ ]) yẽdẽ_fe equal_to_first).
Qed.

Example yẽdẽ_is_big : meaning (adjsense big) [ Yẽdẽₘ ].
Proof.
  apply root.
  apply rootₘ.
  apply Yẽdẽ_is_Mₘ.
  reflexivity.
  discriminate.
  apply bigr.
  reflexivity.
Qed.

Example yẽdẽka_fe : FEₘₚ ([ ka₁ₘ ; Yẽdẽₘ ], [ kaₚᵣ ; yẽdẽₚᵣ ]).
Proof.
  apply yẽdẽMP.  
Qed.

Example Yẽdẽka_is_Mₘ : Mₘ [ ka₁ₘ ; Yẽdẽₘ ].
Proof.
  assert (equal_to_first : ([ ka₁ₘ ; Yẽdẽₘ ] = fst ([ ka₁ₘ ; Yẽdẽₘ ], [ kaₚᵣ ; yẽdẽₚᵣ ]))).
  reflexivity.
  apply (Mₘ_are_FE_fst [ka₁ₘ ; Yẽdẽₘ] ([ ka₁ₘ ; Yẽdẽₘ ], [ kaₚᵣ ; yẽdẽₚᵣ ]) yẽdẽka_fe equal_to_first).
Qed.

Example yẽdẽka_is_big_rock : meaning (adjsense (big AND rock)) [ ka₁ₘ ; Yẽdẽₘ ].
Proof.
  apply root.
  apply rootₘ.
  apply Yẽdẽ_is_Mₘ.
  reflexivity.
  discriminate.
  apply bigr.
  reflexivity.
Qed.





(* The type of sign paradigm entries *)

Definition spₛₚ := (ϕ * τ * sense).


(* Definition lexmeaning : list (lₗ * sense) :=  *)
(*   cons (ñeneₗ, existT Sns (func ent prp) big) *)
(*        (cons (ñeneₗ, existT Sns (func ent prp) tall) *)
(*              (cons (giitaₗ, existT Sns (func ent prp) small) nil)). *)

(* Definition catmeaning : list (mₘ * sense) := *)
(*   cons (poₘ, existT Sns (func ent prp) boat) *)
(*        (cons (poₘ, existT Sns (func ent prp) hand) nil). *)

(* Definition conjmeaning (α β : e → prop) : (e → prop) := *)
(*   λ γ,(α γ) AND (β γ). *)
  
(* Inductive meaning : sense → lₗ → mₘ → Prop := *)
(*   m₁ : ∀ s l m, m = baseₘ → In (l, s) lexmeaning → meaning s l m *)
(* | m₂ : ∀ (s₁ : e → prop) (s₂ : e → prop) l m, *)
(*     m = poₘ → *)
(*     In (l, existT Sns (func ent prp) s₁) lexmeaning → *)
(*     In (m, existT Sns (func ent prp) s₂) catmeaning → *)
(*     meaning (existT Sns (func ent prp) (conjmeaning s₁ s₂)) l m. *)


Inductive meaning : sense → list mₘ → Prop :=
  m₁ : ∀ s m, m = [ROOTₘ] → In s lexmeaning → meaning s m
| m₂ : ∀ (s₁ : e → prop) (s₂ : e → prop) l m,
    m = poₘ →
    In (l, existT Sns (func ent prp) s₁) lexmeaning →
    In (m, existT Sns (func ent prp) s₂) catmeaning →
    meaning (existT Sns (func ent prp) (conjmeaning s₁ s₂)) l m.

(** A type alias for an LCG sign. *)

(** A rule schema for form to sign mappings. *)

Definition ruleₛₚ (catₘ : list m) (kₖ : K) (t : τ) (s : stat_term) :=
  λ (α : structₘₚ)
    (fe : FEₘₚ α)
    (ss : stat_term)
    (β : Sns ss)
    (γ : Sns ss → Sns s)
    (proofₘ : (fst α) ≤ₘ catₘ)
    (proofₖ : klass (fst α) ≤ₖ kₖ)
    (proofₛ : meaning (existT Sns ss β) (fst α)),
    (η (applyₚᵣ (snd α)), t, existT Sns s (γ β)).

(** A sign paradigm is an equivalence class. *)

Inductive Pₛₚ : spₛₚ → spₛₚ → Prop :=
| inₛₚ : ∀ α β l, SPₛₚ α l → SPₛₚ β l → Pₛₚ α β
| reflₛₚ : ∀ α l, SPₛₚ α l → Pₛₚ α α
| transₛₚ : ∀ α β γ, Pₛₚ α β → Pₛₚ β γ → Pₛₚ α γ
| symₛₚ : ∀ α β, Pₛₚ α β -> Pₛₚ β α.
