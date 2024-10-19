(** * Wao Tededo Fragment for Dissertation

This file provides a morphological fragment of Wao Terero pattern
using a version of my theoretical framework as it was defined at the
time of my dissertation. *)

(** The quasi phonemic representation of morphological forms use the
string definition from the standard library. *)

Require Import Coq.Strings.String.

(** I use unicode in this file. *)

Require Import Coq.Unicode.Utf8.

(** I use lists as a convenient data structure. *)

Require Import Coq.Lists.List.
Import Coq.Lists.List.ListNotations.

Open Scope type_scope.
Open Scope string_scope.


(** `m` are basic symbols used as morph categories, where a morph is a
morphological process. Types, functions and relations that manipulate
`m` and collections of `m` will have ₘ in their name. The comments
beside the `m` constructors below are not intended to 'define' the
catagories, but to provide some intuition about which meanings and
forms the element is commonly associated with.

Form paradigm members are categorized using a pair of a list of `m`
and a corresponding list of processes. Lists provide an order, which
allows for some notion of simple scope. I view it as more like a
record of rule application. Categories that appear earlier in the list
do not necessarily correspond to morphs that occur earlier (to the
left) in a word. The record is examined to determine form class, for
instance whether an item can receive nominal or verbal inflection
depending on some derivational category that may exist at the proper
position in the record. This can be done without providing a list that
provides such an order but the order reduces the number of `m` needed,
since morphotactically [c₁, c₂] can be interpretted as distinct from
[c₂, c₁]. It would be possible to use more category names an use a
simple set but I feel there is an inherent notion of before and after
in natural language, which is useful to abstract over but cannot be
ignored. I am aware of no formal theory of morphology that ignores
some notion of order and no system that captures derivational
processes that is devoid of some concept of scope. In a theory like
PFM, which relies on the notions of lexeme and stem, properties of
those potentially morphologically complex entities affect the patterns
of inflection that the theory describes, leaving derivational scope
implicit. It is also the case that [c₁, c₂] versus [c₂, c₁] may also
signal some conventional semantic scope, though this is not
necessarily the case. Such patterns are easier to describe if there is
some preservation of the order of rule application.

A morphological process may have more than one morph category
associated with it. So a process p may be associated with category c₁
or c₂, depending on the definition of a rule. For instance, kã is used
both as a lexical suffix and as the sentient third person, where its
distribution and interpretation are distinct. Therefore a single
category would be sufficiently ambiguous so as to complicate
morphotactic description. It may be that in some cases when a single
process p is associated with c₁ or c₂ that some analysis that
collapses the two categories to a single category would be
possible. For the sake of simplicity, and in order to more clearly
delineate distributional domains -- for instance the domain of lexical
suffix distributions and person suffix distributions -- I do not
pursue such analyses unless they provide some interesting insight into
the morphological system that justifies the move. Although I will not
do so, rules may also associate a single process with multiple `m`. A
process p may be associated with c₁ and c₂ ([c₁, c₂]), which might be
advantageous when there is a cummulative morph of some kind. There are
other ways of representing morphs that signal multiple cummulated
meanings but the framework as it stands leaves this open to stylistic
choice. This should make it clear that even prior to interpretting
morphs in terms of their syntactic and semantic distributions and
signals that processes do not stand in 1-to-1 correspondence with a
category.

Form paradigm members are categorized using lists of `m`. The list is
a convenient data structure within the context of a computer
programming language, or when induction is frequently used in proofs,
type definitions and pattern matching functions. Lists are not the
perfect match for the qualities a collection of `m` should have when
categorizing form-paradigm members. The data structure advantageously
preserves the order in which elements are appended as a series of
`cons`. The list is inconvenient because it allows more than one of
the same element to be added. There should be no more than one of the
same `m` within a compound category for a form-paradigm member. This
means that [ boₘ ] is legal but not `[ boₘ, boₘ ]`. In future
revisions, I may define somethings similar to `Coq.Lists.ListSet`,
which are finite sets implemented as lists. The issue with that data
structure is that despite maintaining the uniqueness of every element
of the set, and despite a list having a natural order, the order is
not respected in the implementation of functions that perform
operations on the data structure. So, something new needs to be
defined to ensure that collections of `m` have the desired properties.

I make due with an imperfect data structure because some
implementation details are not very important at this stage in the
formalization of the morphological theory. For that reason, I have an
ad hoc solution. The list data structure is used, but I define a
wrapper for append such that appending fails if any of the `m` in the
list one is attempting to append already exists in the target
list. So, `appendₘ [1, 2] [3, 4] = [1, 2, 3, 4]` but `appendₘ [1, 2]
[2, 3, 4] = [2, 3, 4]`.

For every free form in the lexicon, there is a category made up of a
list of the elements below. For instance, the item "dika" has a list
category of [ ka₁ₘ, Diₘ ]. The processes of unalayzable stems are
given with an initial upper case letter. Not every list is a
grammatical category, for that reason, the type constructor Mₘ is used
as a predicate These elements are used for form categories, but are
not categories themselves. A morphological category is a list of
elements under the type constructor Mₘ. Each element c *)

Inductive m : Set :=
| Ãₘ (* The bound stem of the noun 'plant' and verb 'say'. *)
| Adoₘ (* The stem of 'same' and the numeral 'one'. *)
| Diₘ (* The bound stem of the noun 'stone'. *)
| Dãtaₘ (* The stem of the verb 'to ache'. *)
| Ĩₘ (* The stem of the copula, short third person pronouns and the distal demonstrative. *)
| Keₘ (* The stem of the verb 'to do'. *)
| Kẽₘ (* The stem of the verb 'to eat' or 'to cut'. *)
| Peẽₘ (* The bound stem for the noun 'plantain'. *)
| Tõbẽₘ (* The stem of long form pronouns. *)
| Wiₘ (* The bound stem of the noun 'canoe'. *)
| Yẽdẽₘ (* The stem of the adjective 'big'. *)
(* Lexical suffixes *)
| bõ₁ₘ (* The 'seed' lexical suffix. *)
| dẽₘ (* The 'food' lexical suffix. *)
| kaₘ (* The 'fruit' lexical suffix. *)
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
| Lxₘ (* Ending in a lexical suffix. *)
| Prₘ (* Ending in a person suffix. *)
| Leafₘ (* A singleton. *)
| Infyₘ (* A stem for inflection. *)
| LSyₘ (* A stem for lexical suffixes. *)
| Nirstyₘ (* Not a first person stem. *)
| Numberableₘ (* A stem for number suffixes. *)
| Doubleableₘ (* A stem for the dual. *)
| Plurableₘ. (* A stem for the feminine suffix. *)

(** Below I define boolean equality of `m`. The `+` is the disjoint
sum constructor. Both equality (`=`) and inequality (`≠`) of `m` are
of type Prop, for instance, Lxₘ = Lxₘ : Prop. Within constructive
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

Example eq_kaₘ : eqₘ kaₘ kaₘ = true.
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
never in morphological rules. I call the `m` that correspond to
particular morphological processes "concrete". Other categories are used
to provide super categories for leaf categories. I call these
categories "abstract" categories and it is usefult to be able to refer
to a list of them. *)

Definition abstractsₘ : list m :=
  [ Lxₘ ;
    Prₘ ;
    Leafₘ ;
    Infyₘ ;
    LSyₘ ;
    Nirstyₘ ;
    Numberableₘ ;
    Doubleableₘ ;
    Plurableₘ
  ].

(** There are other `m` that are usefully grouped to make the rules
that define the partial order on `Mₘ` more succinct. *)

(** `lxsₘ` is a list of lexical suffixes. *)

Definition lxsₘ : list m :=
  [ bõ₁ₘ ;
    dẽₘ ;
    kaₘ ;
    kã₁ₘ ;
    pa₁ₘ ;
    poₘ ;
    pẽₘ ;
    ta₁ₘ ;
    wẽₘ
  ].

(** `nirstsₘ` are affixes used for non-first person person and number marking. *)

Definition nirstsₘ : list m :=
  [ biₘ ;
    bĩₘ ;
    daₘ ;
    dãₘ ;
    diₘ ;
    kã₂ₘ
  ].

(** `personsₘ` are all person marking. *)

Definition personsₘ : list m := boₘ :: bõ₂ₘ :: nirstsₘ.

(** Relationships between abstract Mₘ. *)

Definition abstract_le_rulesₘ : (list (list m * list m)) :=
  [ ([Lxₘ],[LSyₘ]) ;
    ([Leafₘ], [LSyₘ]) ;
    ([LSyₘ], [Infyₘ]) ;
    ([LSyₘ], [Doubleableₘ]) ;
    ([Numberableₘ], [ Doubleableₘ]) ;
    ([Numberableₘ], [ Plurableₘ]) ;
    ([Prₘ], [ Infyₘ]) ;
    ([LSyₘ], [ Nirstyₘ])
  ].

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

Definition inabₘ (α : list m) (β : list m) : bool :=
    match α, β with
    | [], _ => false
    | _, [] => false
    | _ :: _ :: _, _ => false
    | _, _ :: _ :: _ => false
    | [x], [y] => inabbₘ x y abstract_le_rulesₘ
    end.

Definition hdIn (l₁ : list m) (l₂ : list m) : bool :=
  match l₁ with
  | [] => false
  | x :: _ => inₘ x l₂
  end.

Definition isNirstyₘ (l₁ : list m) : bool :=
  match l₁ with
  | [] => false
  | [x] => false
  | x :: y :: _ => andb (inₘ x nirstsₘ) (negb (eqₘ y bõ₂ₘ))
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
(* All non-abstract singleton Mₘ are ≤ₘ [ Leafₘ ]. (hd Leafₘ α) is for
retrieving the `m` as the list head. The occurance of Leafₘ is a
default value required by the `hd` function for the case where α is
nil. *)
| leafₘ : ∀ α, Mₘ α → length α = 1 → ~ hdIn α abstractsₘ = true → leₘ α [Leafₘ]
(* When the last process was a lexical suffix process, the category is
a subcategory of Mₘ [Lxₘ]. *)
| lxₘ : ∀ α, Mₘ α → hdIn α lxsₘ = true → leₘ α [Lxₘ]
(* When the last `m` corresponds to person marking, the category is a
subcategory of Mₘ [Prₘ]. *)
| prₘ : ∀ α, Mₘ α → hdIn α personsₘ = true → leₘ α [Prₘ]
(* bõ₂ₘ and bĩₘ correspond to stem endings where person number affixes
may be added. Note, either plural or dual may be added to such
stems. Only plural may be added to a stem with dãₘ. See below. *)
| numerableₘ : ∀ α, Mₘ α → hdIn α [bõ₂ₘ;bĩₘ] = true → leₘ α [Numberableₘ]
(* The placement of the past tense morph depends on whether or not the
person marking on a verb is first person or otherwise. *)
| nirstyₘ : ∀ α, Mₘ α → isNirstyₘ α = true → leₘ α [Nirstyₘ]
(* The affix dãₘ may be followed by plural marking. *)
| dãplₘ : ∀ α, Mₘ α → hdIn α [dãₘ] = true → leₘ α [Plurableₘ]
(* The relation between abstract Mₘ is listed separately. *)
| abstract_leₘ : ∀ α β, inabₘ α β = true → leₘ α β.

Axiom antisymₘ : ∀ α β : (list m), leₘ α β → leₘ β α → α = β.

Infix "≤ₘ" := leₘ (at level 60, right associativity).

Example leq_is_refl : [Lxₘ] ≤ₘ [Lxₘ].
Proof.
  apply reflₘ.
  apply Mₘ_abstractsₘ.
  simpl.
  reflexivity.
Qed.

Example leq_lx_lsy : [Lxₘ] ≤ₘ [LSyₘ].
Proof.
  apply abstract_leₘ.
  simpl.
  reflexivity.
Qed.

(** K are names of form classes, similar in concept to inflection
classes. The uppercase kappa `K' is a mnemonic for /klæs/.  Like ₘ the
ₖ is used for names of types, functions and relations associated with
K.  Variables of type K are written as κ or κₙ. The noneₖ class is for
the nil case of a list of categories. It has no theoretical
meaning. *)

Inductive K : Set :=
| ãₖ
| kẽₖ
| plantyₖ
| eatyₖ
| bodyₖ
| nounₖ
| adjₖ
| adj₁ₖ
| adj₂ₖ
| verbₖ
| noneₖ. 

Definition K_dec : ∀ α β : K, {α = β} + {α ≠ β}.
Proof. decide equality. Defined.
Definition eqₖ α β := if K_dec α β then true else false.

Example eq_eatyₖ : eqₖ eatyₖ eatyₖ = true.
Proof. compute. reflexivity. Qed.

Definition le_rulesₖ : list (K * K) :=
  [ (ãₖ, plantyₖ) ;
    (ãₖ, verbₖ) ;
    (kẽₖ, verbₖ) ;
    (kẽₖ, plantyₖ) ;
    (kẽₖ, eatyₖ) ;
    (kẽₖ, bodyₖ) ;
    (adj₁ₖ, plantyₖ) ;
    (adj₁ₖ, eatyₖ) ;
    (adj₁ₖ, bodyₖ) ;
    (nounₖ, plantyₖ) ;
    (nounₖ, eatyₖ) ;
    (nounₖ, bodyₖ)
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

Example nounₖ_leq_eatyₖ : nounₖ ≤ₖ eatyₖ.
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
  | [kaₘ ; Diₘ] => nounₖ
  | [wẽₘ ; Ãₘ] => nounₖ 
  | [wẽₘ ; Kẽₘ] => nounₖ
  | [dẽₘ ; Kẽₘ] => nounₖ
  | [x ; Kẽₘ] => match inₘ x lxsₘ with
                 | true => verbₖ
                 | false => kẽₖ
                 end
  | [Ãₘ] => ãₖ
  | [Kẽₘ] => kẽₖ
  | [x ; Yẽdẽₘ] => match inₘ x lxsₘ with
                   | true => adj₂ₖ
                   | false => adj₁ₖ
                   end
  | [Yẽdẽₘ] => adj₁ₖ
  | [Keₘ] => verbₖ
  | _ :: t => klass t
  end.

Example yẽdẽka_klass : klass [kaₘ ; Yẽdẽₘ] = adj₂ₖ.
Proof. compute. reflexivity. Qed.

Example yẽdẽ_klass : klass [Yẽdẽₘ] = adj₁ₖ.
Proof. compute. reflexivity. Qed.

Example yẽdẽbo_klass : klass [boₘ ; Yẽdẽₘ] = adj₁ₖ.
Proof. compute. reflexivity. Qed.

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

Definition rule1ₘₚ (catₘ : list m) (κ : K) (newₘ : list m) (newₚᵣ : list processₚᵣ) :=
  λ (α : structₘₚ)
    (proofₘ : fst α ≤ₘ catₘ)
    (proofₖ : klass (fst α) ≤ₖ κ),
    combineₘₚ newₘ (fst α) newₚᵣ (snd α).

(* I am still not sure how I want to do this.
Definition rule2ₘₚ (catₘ : list m) (κ : K) (newₘ : list m) (newₚᵣ : list processₚᵣ) :=
  λ (α : structₘₚ)
    (proofₘ : fst α ≤ₘ catₘ)
    (proofₖ : klass (fst α) ≤ₖ κ),
    (newₘ :: (tail (fst α)), newₚᵣ :: (tail (snd α))). *)

Inductive FEₘₚ : structₘₚ → Prop :=
| kẽMP : FEₘₚ ( [Kẽₘ], [kẽₚᵣ] )
| keMP : FEₘₚ ( [Keₘ], [keₚᵣ] )
| yẽdẽMP : FEₘₚ ( [Yẽdẽₘ], [yẽdẽₚᵣ] )
| dikaMP : FEₘₚ ( [kaₘ ; Diₘ], [kaₚᵣ ; di₁ₚᵣ] )
(*| peẽdẽMP : FEₘₚ ( [dẽₘ ; Peẽₘ], [dẽₚᵣ ; peẽₘ] )*)
| ãMP : FEₘₚ ( [Ãₘ], [ãₚᵣ] )
| kaMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [LSyₘ] bodyₖ [kaₘ] [kaₚᵣ])
                     α proofₘ proofₖ)
| wẽMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [LSyₘ] plantyₖ [wẽₘ] [wẽₚᵣ])
                     α proofₘ proofₖ)
| dẽMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [LSyₘ] eatyₖ [dẽₘ] [dẽₚᵣ])
                     α proofₘ proofₖ)
| kã₁MP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [LSyₘ] bodyₖ [kã₁ₘ] [kãₚᵣ])
                     α proofₘ proofₖ)
| kã₂MP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [LSyₘ] verbₖ [kã₂ₘ] [kãₚᵣ])
                     α proofₘ proofₖ)
| boMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [LSyₘ] verbₖ [boₘ] [boₚᵣ])
                     α proofₘ proofₖ)
| bõ₂MP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [LSyₘ] verbₖ [bõ₂ₘ] [bõₚᵣ])
                     α proofₘ proofₖ)
| biMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [LSyₘ] verbₖ [biₘ] [biₚᵣ])
                     α proofₘ proofₖ)
| bĩMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [LSyₘ] verbₖ [bĩₘ] [bĩₚᵣ])
                     α proofₘ proofₖ)
| daMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [Doubleableₘ] verbₖ [daₘ] [daₚᵣ])
                     α proofₘ proofₖ)
| dãMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [LSyₘ] verbₖ [dãₘ] [dãₚᵣ])
                     α proofₘ proofₖ)
| diMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [Plurableₘ] verbₖ [diₘ] [di₂ₚᵣ])
                     α proofₘ proofₖ)
| paMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [Infyₘ] verbₖ [pa₂ₘ] [paₚᵣ])
                     α proofₘ proofₖ)
| tapaMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [Nirstyₘ] verbₖ [pa₂ₘ ; ta₂ₘ] [paₚᵣ ; taₚᵣ])
                     α proofₘ proofₖ)
| tabõMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [LSyₘ] verbₖ [bõ₂ₘ ; ta₂ₘ] [bõₚᵣ ; taₚᵣ])
                     α proofₘ proofₖ)
| taboMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ [LSyₘ] verbₖ [boₘ ; ta₂ₘ] [boₚᵣ ; taₚᵣ])
                     α proofₘ proofₖ).

(** Anything that is proveably a form paradigm member has a validly
named compound category. *)

Definition FEM : ∀ α : structₘₚ, FEₘₚ α → Prop :=
  λ (α : structₘₚ) (_ : FEₘₚ α), Mₘ (fst α).

(* I am not yet sure how I want to do this:

Fixpoint stemof (α : list m) : option m :=
  match α with
  | nil => None
  | head :: tail =>
      match (find (eqₘ head) stems) with
      | None => stemof tail
      | something => something
      end
  end.

Definition optional_stem_eq (α : option m) (β : option m) : bool :=
  match α, β with
  | None, _ => false
  | _, None => false
  | Some x, Some y => eqₘ x y
  end.

Definition eq_stem (α : structₘₚ) (β : structₘₚ) : bool :=
  match α, β with
  | (x, _), (y, _) => optional_stem_eq (stemof x) (stemof y)
  end.

Definition S (α : structₘₚ) (β : structₘₚ) : Prop :=
  eq_stem α β = true.

Inductive FPₘₚ : structₘₚ → structₘₚ → Prop :=
| inₘₚ : ∀ α β, S α β → FEₘₚ α → FEₘₚ β → FPₘₚ α β
| 
*)  

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

(* I am going to provide this functionality at the interface
only. Rule schema 2 will not work if I can't trust that there is a
correspondence between categories and processes at the morphological
level.

| cat_equivₘₚ : ∀ α β : structₘₚ, Mₘ (fst α) → Mₘ (fst β) → equivₘₚ α
  β → equivₘₚ α (fst β, snd α).
*)

Infix "≡ₘₚ" := equivₘₚ (at level 90).

(** Here I wish to prove that not only the left side of the
equivalence (α) but also the right side (β) has category equivalence.
If two structures are string equivalent, then the left side structure
may have its compound category replaced with the compound category of
the right side structure, as stated in `cat_equivₘₚ'.  Due to the
symmetric property of the equivalence, the right side structure may
also have its compound category replaced with the compound category of
the left side structure. *)

Lemma rev_cat_equivₘₚ : ∀ α β : structₘₚ, α ≡ₘₚ β → β ≡ₘₚ (fst α, snd
β).  Proof.  (** The statement `intros α β H' introduces the variables
and the hypothesis α ≡ₘₚ β.  This results in the following labeled
hypotheses and goal.  *)

  (** α, β : structₘₚ H : α ≡ₘₚ β ============================ β ≡ₘₚ
     (fst α, snd β)

   *) intros α β H.
  
  (** The statement `apply symₘₚ in H' applies the type constructor to
  the hypothesis H.

     This results in the order of the variables in the hypothesis H
   being flipped.  *)

  (** α, β : structₘₚ H : β ≡ₘₚ α ============================ β ≡ₘₚ
     (fst α, snd β)

   *) apply symₘₚ in H.
  
  (* The statement `apply cat_equivₘₚ in H' applies the type
  constructor to the hypothesis H.

     This results in the hypothesis H being identical to the goal.

     α, β : structₘₚ H : β ≡ₘₚ (fst α, snd β)
     ============================ β ≡ₘₚ (fst α, snd β)

   *) apply cat_equivₘₚ in H.

  (* The `assumption' tactic causes the proof assistant to look for a
     type that is convertable to the goal in the context.  In this
     case H is trivially convertable.  *) assumption.  Qed.

(** The next two proofs demonstrate that the string equivalence
definition results in the equivalence of the processes that produced
the identical strings. *)

Lemma proc_equivₘₚ : ∀ α β : structₘₚ, α ≡ₘₚ β → α ≡ₘₚ (fst α, snd β).
Proof.  intros α β H.

  (* The statement `apply rev_cat_equivₘₚ in H as I' applies the
     previous lemma to the hypothesis H.  The result of the
     application is labeled I so that both hypothesis can be
     referenced later.

     The result is the following set of hypotheses and goals.

     α, β : structₘₚ H : α ≡ₘₚ β I : β ≡ₘₚ (fst α, snd β)
     ============================ α ≡ₘₚ (fst α, snd β) *) apply
     rev_cat_equivₘₚ in H as I.

  (* The statement `apply transₘₚ with α β (fst α, snd β) in I'
  applies the type constructor for transitivity, explicitly specifying
  the arguments.

     This results in I being identical to goal.  The proof assistant
     requires the second goal to be proven due to the definition of
     `transₘₚ'.  The second goal corresponds to H.  Both goals can be
     solved by assumption.

     α, β : structₘₚ H : α ≡ₘₚ β I : α ≡ₘₚ (fst α, snd β)
     ============================ α ≡ₘₚ (fst α, snd β)

     goal 2 is: α ≡ₘₚ β
 
   *) apply transₘₚ with α β (fst α, snd β) in I.  assumption.
  assumption.  Qed.

(** The lemma for the reverse case of `proc_equivₘₚ' only requires the
symmetric property of `≡ₘₚ' to be proven. *)

Lemma rev_proc_equivₘₚ : ∀ α β : structₘₚ, α ≡ₘₚ β → β ≡ₘₚ (fst β, snd
α).  Proof.  intros α β H.  apply symₘₚ in H.  apply proc_equivₘₚ in H
as I.  assumption.  Qed.
