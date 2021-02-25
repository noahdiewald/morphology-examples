(** * Cochabamba Quechua Plurals

Below is a morphological fragment of in Lexical Proof Morphology of an
overabundant plural pattern found in Cochabamba Quechua.

In some dialects of Cochabamba Quechua the borrowed Spanish plural -s
occurs on all nominal stems that end in a vowel. There is also a
native plural -kuna, that occurs on nominal stems generally. These
plural may also co-occur in varying order on the stem. So for a vowel
stem, like warmi, 'woman', warmi-s, warmi-kuna, warmi-s-kuna,
warmi-kuna-s are all predicted to occur, though not with equal
likelihood, necessarily. A stem that ends in a consonant, like sipas,
'young woman', is predicted to have the plural forms sipaskuna and
sipaskunas for some speakers. There is also a possible semantic
constraint on the distribution of the Spanish plural, where the -kuna
plural is more appropriate for contrastive subjects. Of course, there
are also other dialectal patterns and speaker variation. The fragment
below captures one observable pattern. *)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Open Scope type_scope.
Open Scope string_scope.

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

The lexeme WARMI corresponds to a nominal with a stem ending in a
vowel. The lexeme SIPAS corresponds to a lexeme ending in a
consonant. *)

Inductive lexeme : Set :=
| WARMI : lexeme (* woman *)
| SIPAS : lexeme. (* young woman *)

(** ** Morphological categories

The type matom is for atoms used in m-category names or mcats,
which I compose like lists. Mcats are morphological categories, which
categorize observable analogical patterns in morphological form. For
instance, though warmis, warmikuna, warmiskuna and warmikunas
correspond to two syntactic categories, one for basic plural and one
for a contrastive subject, but there are, at minimum, four
morphological categories, one for each form. In practice, there are
more categories to capture the "morphotactics" or the allowable
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
| nbase : matom
| mplural : matom
| s : matom
| kuna : matom
| kbase : matom
| sbase : matom
| ta : matom.

(** As stated above, mcat is a list of matoms. *)

Definition mcat := list matom.

** Mcats for the fragment *)

(* [ nbase ] is a basic noun stem.  [ kbase ] is a stem that can take
   a -kuna affix.  [ sbase ] is a stem that can take a -s affix.  [
   kuna ] is any form that contains -kuna.  [ mplural ] is any form
   with a plural affix.  [ s , nbase ] is a basic stem with only an -s
   affix.  [ kuna, nbase ] is a basic stem with only a -kuna affix.
   The other two mcats contain both suffixes in differing order.

The kuna forms are hypothesized to have a different distribution than
the -s only form. They are (possibly) more compatible with focus
constructions in subject position.

A take away for the above is that nearly every form type has its own
category, at least in this analysis of this phenomenon. Labeling form
types is not the only role of these categories. Some categories, such
as [ sbase ] and [ kbase ] are only directly relevant to
morphotactics. Other categories, such as [ kuna ] are more relevant to
the interface with the syntactic paradigm. *)

(** ** Morphological forms

An mform, or morphological form, is a string *)

Definition mform := string.

(** Below are some string functions to handle suffixation. *)

Definition suffix_s (stem:mform) : mform :=
  stem ++ "s".

Definition suffix_kuna (stem:mform) : mform :=
  stem ++ "kuna".

Definition suffix_ta (stem:mform) : mform :=
  stem ++ "ta".

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

Check ( [ kuna ] , "foot" , WARMI ).

(** Here I define Fentry, which is a predicate that is proveable when
an mtrip is a valid lexical entity. *)

Axiom Fentry : mtrip -> Prop.

(** Here I define the mtrip for the "warmi" stem. I am not handling
the phonological dimension that "sipas" requires, where -s cannot be
suffixed to a stem that ends in a consonant because I haven't built a
phonological abstraction into this example, yet. I could specify the
needed categorical distinction with a predicate. Such a predicate
would be true for some specified set of mforms and false for others
but it is more interesting to do it correctly and pattern match on the
string. *)

Definition warmi_nbase := ([ nbase ], "warmi", WARMI) : mtrip.

(** This requires an explicit axiom to be treated like an
Fentry. Other Fentries will be derived from it. *)

Axiom f_warmi_nbase : Fentry warmi_nbase.

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

Axiom nbase_lem_kbase : lem [ nbase ] [ kbase ].
Axiom s_nbase_lem_kbase : lem [ s ; nbase ] [ kbase ].
Axiom nbase_lem_sbase : lem [ nbase ] [ sbase ].
Axiom kuna_nbase_lem_sbase : lem [ kuna ; nbase ] [ sbase ].
Axiom kuna_nbase_lem_kuna : lem [ kuna ; nbase ] [ kuna ].
Axiom kuna_s_nbase : lem [ kuna ; s ; nbase ] [ kuna ].
Axiom s_kuna_nbase : lem [ s ; kuna ; nbase ] [ kuna ].
Axiom kuna_lem_mplural : lem [ kuna ] [ mplural ].
Axiom s_nbase_lem_mplural : lem [ s ; nbase ] [ mplural ].

(** ** Morphotactic rules

In using the word "morphotactic", it may imply an imperative form
building interpretation. Though rules in this system tend to take as
input simpler forms and output more complex forms, the opposite is
possible. Defining rules in a form building direction is done for
practical reasons. Longer more complex forms are often less
frequent. If one wishes to base the assumed forms of a fragment on
something that is independently observable and to be consistent about
which forms are assumed as axioms across lexemes, frequently used
forms are preferable -- or perhaps something like the principal parts
of a paradigm. The intended interpretation of these rules is that they
declare that if it is the case that Fentry x exists, then Fentry y
exists but x does not underly y in any sense. Nor is it necessarily
contained as a subpart of y.

Below one can see the first morphotactic rule, which I call form-form
mappings. It specifies that anything within the category of [ sbase ]
can have its form suffixed with -s. The accessors that look like (fst
(fst mt)) are because the mtrip triple is actually a pair of a pair
and a lexeme, the structure is w=((x,y),z) so (fst (fst w)) is x. In
English the rule says, for any mtrip that is an Fentry, if the mcat is
less than or equal to [ sbase ] then there is a Fentry such that the
category is whatever was provided with matom s added to the front, an
mform with an affixed -s and an unchanged lexeme. *)

Axiom add_s : forall
    (mt : mtrip), (Fentry mt) ->
                  (lem (fst (fst mt)) [ sbase ]) ->
                  Fentry (cons s (fst (fst mt)),
                          suffix_s (snd (fst mt)),
                          (snd mt)).

(** The rule below is very similar except that it is for the -kuna
containing forms. *)

Axiom add_kuna : forall
    (mt : mtrip), (Fentry mt) ->
                  (lem (fst (fst mt)) [ kbase ]) ->
                  Fentry (cons kuna (fst (fst mt)),
                          suffix_kuna (snd (fst mt)),
                          (snd mt)).

(** The below specifies the morphological category for accusative
marked plurals. *)

Axiom add_plta : forall
    (mt : mtrip), (Fentry mt) ->
                  (lem (fst (fst mt)) [ mplural ]) ->
                  Fentry ([ s ; ta ],
                          suffix_ta (snd (fst mt)),
                          (snd mt)).

(** The below specifies the morphological category for accusative
marked singulars. *)

Axiom add_ta : forall
    (mt : mtrip), (Fentry mt) ->
                  (lem (fst (fst mt)) [ nbase ]) ->
                  Fentry ([ ta ],
                          suffix_ta (snd (fst mt)),
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
| nom : matom
| nom_pl : matom
| nom_foc_pl : matom
| acc : matom
| acc_pl : matom.

Axiom Sentry : syncat -> Prop.

(** ** Interface rules

I call these form-sign mappings because the lexical entries are called
signs in LCG.

The first maps uninflected forms to the unmarked nominative. The
second, assuming that the -kuna forms are not always focal, which is
consistent with corpora, maps all mplurals to nom_pl. The third maps
the kuna forms to nom_foc_pl. The last two map -ta marked forms to the
acc and acc_pl, respectively. *)

Axiom nbase_to_nom : forall
    (mt : mtrip), (Fentry mt) ->
                  (lem (fst (fst mt)) [ nbase ]) -> Sentry nom.

Axiom mplural_to_nom_pl : forall
    (mt : mtrip), (Fentry mt) ->
                  (lem (fst (fst mt)) [ mplural ]) -> Sentry nom_pl.

Axiom kuna_to_foc : forall
    (mt : mtrip), (Fentry mt) ->
                  (lem (fst (fst mt)) [ kuna ]) -> Sentry nom_foc_pl.

Axiom ta_to_acc : forall
    (mt : mtrip), (Fentry mt) ->
                  (lem (fst (fst mt)) [ ta ]) -> Sentry acc.

Axiom s_ta_to_acc_pl : forall
    (mt : mtrip), (Fentry mt) ->
                  (lem (fst (fst mt)) [ s ; ta ]) -> Sentry acc_pl.
