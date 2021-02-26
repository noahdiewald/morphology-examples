(** * Wao Tededo Future

Below is a morphological fragment of in Lexical Proof Morphology of an
overabundant future tense pattern found in Wao Tededo (Terero).

In Wao Tededo there is a pattern where both a synthetic form bekebopa,
'I will drink' and an analytic construction beke kebopa, can be used
in the formation of the future tense. There is much to be learned
about this pattern but the two forms are considered replaceabl by some
native speakers when context is controlled for. This indicates a
shared category of the two constructions when used in syntax. *)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Open Scope type_scope.  Open Scope string_scope.

(** * Initial axioms of the fragment

Below I introduce the basic lexemes and categories of the
morphological fragment.

** Lexemes

First I define some basic lexemes. Lexemes have no inherent
properties. They serve a role similar to foriegn keys in a relational
database. They are a key for retrieving and defining collections of
information. For instance ( LEXEME_1, x ), ( LEXEME_1, y ) puts both x
and y in the same collection, where the collection is defined in terms
of the second elements of tuples where the first element is the same
lexeme.

The lexeme BEKI corresponds to a verb meaning 'drink'. The lexeme
KEKI corresponds to an auxiliary used to form the future tense. *)

Inductive lexeme : Set :=
| BEKI : lexeme (* drink *)
| KEKI : lexeme. (* do *)

(** ** Morphological categories

The type matom is for atoms used in m-category names or mcats, which I
compose like lists. Mcats are morphological categories, which
categorize observable analogical patterns in morphological form. There
are categories used to capture the "morphotactics" or the allowable
patterns of affix coocurence within words of the system and to allow
for generalizations when mapping between syntactic categories.

In fact, what one "sees" in this system are not the categories,
themselves, which are conceptually atomic but a means of referring to
them with names. Think of the name John Smith as a category name and
Smith as analogous to an matom. Just as the last name Smith can belong
to an entire family or even multiple people in multiple families, each
person with Smith in their name is an individual and could,
potentially be named something else. Likewise, having Smith as a last
name, one of the most frequent last names in the English language,
does not entail family membership. Despite this, the system of naming
children using their parents' last names does simplify the naming of
children. Therefore if it were a rule that every child needed to be
named as a composition of the last name of a particular parent and
some individuated name, the rules of naming are greatly simplified,
even if nothing can be said to be entailed about the properties of
that individual by having a particular last name. The category naming
scheme used here, where names are lists of matoms allows for
flexibility and simplification in naming categories using rules but,
at least at this time, no rule applies because it has a particular
sub-element or sub-list, i.e.\ nothing is entailed about the category
just because a sub-element of its name is one thing or another. This
is a fundamental difference between this scheme and a feature system,
for instance. *)

Inductive matom : Set :=
| base : matom
| ke : matom
| bo : matom
| pa : matom
| bostem : matom
| pastem : matom.

(** As stated above, mcat is a list of matoms. *)

Definition mcat := list matom.

(** Mcats for the fragment

[ base ] is a basic, uninflected, stem. [ ke, base ], [ bo, base ],
etc, will be stems with -ke and -bo suffixed respectively. To provide
a little more context, bo is associated with first person, pa with
assertive, a marker of something like the indicative. The ke is used
in various contexts including what I am calling the future. It is also
correlated to an 'in order to' meaning and a limitive 'just' or 'only'
meaning, more often when used with nominals. A take away is that
nearly every form type has its own category, at least in this analysis
of this phenomenon. Labeling form types is not the only role of these
categories they also play a role in morphotactics and the interface. [
bostem ] and [ pastem ] are categories of stems that license stems
ending in bo and pa, respectively. *)

(** ** Morphological forms

An mform, or morphological form, is a string. *)

Definition mform := string.

(** Below are some string functions to handle suffixation. *)

Definition suffix_ke (stem:mform) : mform :=
  stem ++ "ke".

Definition suffix_bo (stem:mform) : mform :=
  stem ++ "bo".

Definition suffix_pa (stem:mform) : mform :=
  stem ++ "pa".

(** ** The structure of morphological paradigm entries

An mtrip is a data structure used to define Fentrys, which are
"form entries" aka morphological paradigm entries. There could
potentially be many non-Fentrys that have the type of an
mtrip. Nothing constrains this type to only be reasonable
entities. One of the purposes of the theory is to specify what
morphological forms are valid in a particular language. This is
similar to the formal language notion of defining the characteristic
function of a subset of all string combinations that correspond to a
grammar.

Here the '*' corresponds to ×, for defining the types of pairs. *)

Definition mtrip := mcat * mform * lexeme.

(** The check below demonstrates why simply saying that we're working
with mtrips is not good enough. Non-grammatical triples check. We need
to be able to specify which are legal triples. *)

Check ( [ ke, base ] , "foot" , KEKI ).

(** Here I define Fentry, which is a predicate that is proveable when
an mtrip is a valid lexical entity. *)

Axiom Fentry : mtrip -> Prop.

(** Here I define the mtrip for the beki and keki stems. *)

Definition beki_base := ([ base ], "be", BEKI) : mtrip.

Definition keki_base := ([ base ], "ke", KEKI) : mtrip.

(** These require an explicit axiom to be treated like an
Fentry. Other Fentries will be derived from it. *)

Axiom f_beki_base : Fentry beki_base.

Axiom f_keki_base : Fentry keki_base.

(** * Morpho-Lexical relations

lem, for "less than or equal to morphological category" is the
order over morphological categories, or mcats. What you see below are
the basic properties of an order. These state the relation is
reflexive, meaning that x ≤ x; antisymmetric, meaning that if x ≤ y
and y ≤ x then x = y; transitive, meaning that if x ≤ y and y ≤ z then
x ≤ z. *)

Axiom lem : mcat -> mcat -> Prop.
Axiom lem_refl : forall x : mcat, lem x x.
Axiom lem_antisym : forall x y : mcat, lem x y -> lem y x -> x = y.
Axiom lem_trans : forall x y z : mcat, lem x y -> lem y z -> lem x z.

(** The order is not natural. There may be natural orders on the
underlying list type based on length but this is not how I use
mcats. As mentioned, though their structure is complex, they are
*names* of atomic categories.

Due to the fact that the order is not natural, each relation must be
explicitly specified, except those that are predictable from the
properties of the order. Below I specify those needed for this
fragment. *)

Axiom base_lem_bostem : lem [ base ] [ bostem ].
Axiom ke_base_lem_bostem : lem [ ke ; base ] [ bostem ].
Axiom bostem_lem_pastem : lem [ bostem ] [ pastem ].
Axiom bo_lem_pastem : lem [ bo ; base ] [ pastem ].
Axiom bo_ke_lem_pastem : lem [ bo ; ke ; base ] [ pastem ].

(** ** Morphotactic rules

In using the word "morphotactic", it may imply an imperative form
building interpretation. Though rules in this system tend to take as
input simpler forms and output more complex forms, the opposite is
possible. Defining rules in a form building direction is done for
practical reasons. Longer more complex forms are often less
frequent. If one wishes to base the assumed forms of a fragment on
something that is independently observable and be consistent about
which forms are assumed as axioms across lexemes, frequently used
forms are preferable -- or alternately, something like the principal
parts of a paradigm. The intended interpretation of these rules is
that they declare that if it is the case that Fentry x exists, then
Fentry y exists. But x does not underly y in any sense. Nor is it
necessarily contained as a subpart of y.

Below one can see the first morphotactic rule, which I call form-form
mappings. It specifies that anything within the category of [ base ]
can have its form suffixed with -ke. The accessors that look like (fst
(fst mt)) are because the mtrip triple is actually a pair of a pair
and a lexeme, the structure is w=((x,y),z) so (fst (fst w)) is x. In
English the rule says, for any mtrip that is an Fentry, if the mcat is
less than or equal to [ base ] then there is a Fentry such that the
category is whatever was provided with matom ke added to the front, an
mform with an affixed -ke and an unchanged lexeme. *)

Axiom add_ke : forall
    (mt : mtrip), (Fentry mt) ->
                  (lem (fst (fst mt)) [ base ]) ->
                  Fentry (cons ke (fst (fst mt)),
                          suffix_ke (snd (fst mt)),
                          (snd mt)).

(** The rule below is very similar except that it is for the -bo
containing forms. *)

Axiom add_kuna : forall
    (mt : mtrip), (Fentry mt) ->
                  (lem (fst (fst mt)) [ bobase ]) ->
                  Fentry (cons bo (fst (fst mt)),
                          suffix_bo (snd (fst mt)),
                          (snd mt)).

(** The below specifies the morphological category for assertives. *)

Axiom add_plta : forall
    (mt : mtrip), (Fentry mt) ->
                  (lem (fst (fst mt)) [ pabase ]) ->
                  Fentry (cons pa (fst (fst mt)),
                          suffix_pa (snd (fst mt)),
                          (snd mt)).

(** * Mock-up of the interface

Below I define some types for syntactic categories but I do not supply
full entries. This is because for the purposes of this simple
exposition it doesn't make sense to embed the actual types and terms
needed for Linear Categorial Grammar, which is the syntactic theory
that I assume.

In order to hold somewhat to the spirit of the complete theory, I
define Sentry which is the predicate for valid lexical entries. *)

Inductive syncat : Set :=
| V_fut_1 : matom
| V_fut_3 : matom
| V_fut_part : matom
| V_fut_part_aux_1 : matom
| V_fut_part_aux_3 : matom.

Axiom Sentry : syncat -> Prop.

(** ** Interface rules

I call these form-sign mappings because the lexical entries are called
signs in LCG.

The first maps basic stems with -ke to the future participle
category. The second maps a basic stem with -pa to the category for
the auxiliary third person, which in a proper treatment would take a
participle as an argument. The third maps a basic stem with -bopa to a
similar category for the first person. The following rules map
morphological categories to the synthetic future tense. *)

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

(** ** An explanation of the syntactic categories

In reality, a verbal syntactic category is generally of the form NP -o
S for an intransitive and NP -o NP -o S for a transitive. Since the
transitivity of the periphrase should be determined by what I am
calling the participal, the actual scheme looks like the following:

|- \lambda t s.s(t)·kebopa;(NP -o V.fut.part) -o NP.1 -o S;\lambda x
   P.fut(P(x))

This lexical entry for kebopa says that it takes an intransitive
future participle and then feeds it a first person argument NP.1.

|- boto;NP.1;first

This is the lexical entry of a first person pronoun.

|- epe;NP;water

The above is the lexical entry for water.

|- \lambda u v.u·v·beke;NP -o NP -o V.fut.part;\lambda w z.drink(z w)

The above is the lexical entry for beke.

First beke is combined with epe using modus ponens resulting in the
following:

|- \lambda u.u·epe·beke;NP -o V.fut.part;\lambda w.drink(water, w)

This is now of the right type to combine with kebopa resulting in:

|- \lambda t.t·epe·beke·kebopa;NP.1 -o S;\lambda x.fut(drink(water,
   x))

The expression can now be combined with the first person:

|- boto·epe·beke·kebopa;S;fut(drink(water first))

The basic notion is that any participal can be made intransitive by
applying one arguement. Agreement can be handled completely by the
auxiliary, which absorbs the subject argument of the participal when
it combines with it.

*)