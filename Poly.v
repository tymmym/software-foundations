(** * Poly: Polymorphism and Higher-Order Functions *)

(* $Date: 2012-09-08 20:51:57 -0400 (Sat, 08 Sep 2012) $ *)

Require Export Lists.

(* ###################################################### *)
(** * Polymorphism *)

(* ###################################################### *)
(** ** Polymorphic Lists *)

(** Up to this point, we've been working with lists of numbers.
    Of course, interesting programs also need to be able to manipulate
    lists whose elements are drawn from other types -- lists of
    strings, lists of booleans, lists of lists, etc.  We _could_ just
    define a new inductive datatype for each of these, for
    example... *)

Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

(** ... but this would quickly become tedious, partly because we
    have to make up different constructor names for each datatype, but
    mostly because we would also need to define new versions of all
    our list manipulating functions ([length], [rev], etc.)  for each
    new datatype definition. *)

(** To avoid all this repetition, Coq supports _polymorphic_
    inductive type definitions.  For example, here is a polymorphic
    list datatype. *)

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

(** This is exactly like the definition of [natlist] from the
    previous chapter, except that the [nat] argument to the [cons]
    constructor has been replaced by an arbitrary type [X], a binding
    for [X] has been added to the header, and the occurrences of
    [natlist] in the types of the constructors have been replaced by
    [list X].  (We can re-use the constructor names [nil] and [cons]
    because the earlier definition of [natlist] was inside of a
    [Module] definition that is now out of scope.) *)

(** What sort of thing is [list] itself?  One good way to think
    about it is that [list] is a _function_ from [Type]s to
    [Inductive] definitions; or, to put it another way, [list] is a
    function from [Type]s to [Type]s.  For any particular type [X],
    the type [list X] is an [Inductive]ly defined set of lists whose
    elements are things of type [X]. *)

(** With this definition, when we use the constructors [nil] and
    [cons] to build lists, we need to tell Coq the type of the
    elements in the lists we are building -- that is, [nil] and [cons]
    are now _polymorphic constructors_.  Observe the types of these
    constructors: *)

Check nil.
(* ===> nil : forall X : Type, list X *)
Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)

(** (Side note on notation: In .v files, the "forall" quantifier is
    spelled out in letters.  In the generated HTML files, [forall] is
    usually typeset as the usual mathematical "upside down A," but
    you'll see the spelled-out "forall" in a few places.  This is just
    a quirk of typesetting: there is no difference in meaning. *)

(** The "[forall X]" in these types should be read as an
    additional argument to the constructors that determines the
    expected types of the arguments that follow.  When [nil] and
    [cons] are used, these arguments are supplied in the same way as
    the others.  For example, the list containing [2] and [1] is
    written like this: *)

Check (cons nat 2 (cons nat 1 (nil nat))).

(** (We've gone back to writing [nil] and [cons] explicitly here
    because we haven't yet defined the [ [] ] and [::] notations for
    the new version of lists.  We'll do that in a bit.) *)

(** We can now go back and make polymorphic (or "generic")
    versions of all the list-processing functions that we wrote
    before.  Here is [length], for example: *)

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length X t)
  end.

(** Note that the uses of [nil] and [cons] in [match] patterns
    do not require any type annotations: we already know that the list
    [l] contains elements of type [X], so there's no reason to include
    [X] in the pattern.  (More formally, the type [X] is a parameter
    of the whole definition of [list], not of the individual
    constructors.  We'll come back to this point later.)

    As with [nil] and [cons], we can use [length] by applying it first
    to a type and then to its list argument: *)

Example test_length1 :
    length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity.  Qed.

(** To use our length with other kinds of lists, we simply
    instantiate it with an appropriate type parameter: *)

Example test_length2 :
    length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity.  Qed.

(** Let's close this subsection by re-implementing a few other
    standard list functions on our new polymorphic lists: *)

Fixpoint app (X : Type) (l1 l2 : list X)
                : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
  | nil      => cons X v (nil X)
  | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
  | nil      => nil X
  | cons h t => snoc X (rev X t) h
  end.

Example test_rev1 :
    rev nat (cons nat 1 (cons nat 2 (nil nat)))
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity.  Qed.

Example test_rev2:
  rev bool (nil bool) = nil bool.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(** *** Type Annotation Inference *)

(** Let's write the definition of [app] again, but this time we won't
    specify the types of any of the arguments. Will Coq still accept
    it? *)

Fixpoint app' X l1 l2 : list X :=
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app' X t l2)
  end.

(** Indeed it will.  Let's see what type Coq has assigned to [app']: *)

Check app'.
Check app.

(** It has exactly the same type type as [app].  Coq was able to
    use a process called _type inference_ to deduce what the types of
    [X], [l1], and [l2] must be, based on how they are used.  For
    example, since [X] is used as an argument to [cons], it must be a
    [Type], since [cons] expects a [Type] as its first argument;
    matching [l1] with [nil] and [cons] means it must be a [list]; and
    so on.

    This powerful facility means we don't always have to write
    explicit type annotations everywhere, although explicit type
    annotations are still quite useful as documentation and sanity
    checks.  You should try to find a balance in your own code between
    too many type annotations (so many that they clutter and distract)
    and too few (which forces readers to perform type inference in
    their heads in order to understand your code). *)

(* ###################################################### *)
(** *** Type Argument Synthesis *)

(** Whenever we use a polymorphic function, we need to pass it
    one or more types in addition to its other arguments.  For
    example, the recursive call in the body of the [length] function
    above must pass along the type [X].  But just like providing
    explicit type annotations everywhere, this is heavy and verbose.
    Since the second argument to [length] is a list of [X]s, it seems
    entirely obvious that the first argument can only be [X] -- why
    should we have to write it explicitly?

    Fortunately, Coq permits us to avoid this kind of redundancy.  In
    place of any type argument we can write the "implicit argument"
    [_], which can be read as "Please figure out for yourself what
    type belongs here."  More precisely, when Coq encounters a [_], it
    will attempt to _unify_ all locally available information -- the
    type of the function being applied, the types of the other
    arguments, and the type expected by the context in which the
    application appears -- to determine what concrete type should
    replace the [_].

    This may sound similar to type annotation inference -- and,
    indeed, the two procedures rely on the same underlying mechanisms.
    Instead of simply omitting the types of some arguments to a
    function, like
      app' X l1 l2 : list X :=
    we can also replace the types with [_], like
      app' (X : _) (l1 l2 : _) : list X :=
    which tells Coq to attempt to infer the missing information, just
    as with argument synthesis.

    Using implicit arguments, the [length] function can be written
    like this: *)

Fixpoint length' (X:Type) (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length' _ t)
  end.

(** In this instance, we don't save much by writing [_] instead of
    [X].  But in many cases the difference can be significant.  For
    example, suppose we want to write down a list containing the
    numbers [1], [2], and [3].  Instead of writing this... *)

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

(** ...we can use argument synthesis to write this: *)

Definition list123' := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* ###################################################### *)
(** *** Implicit Arguments *)

(** If fact, we can go further.  To avoid having to sprinkle [_]'s
    throughout our programs, we can tell Coq _always_ to infer the
    type argument(s) of a given function. *)

Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].
Implicit Arguments length [[X]].
Implicit Arguments app [[X]].
Implicit Arguments rev [[X]].
Implicit Arguments snoc [[X]].

(* note: no _ arguments required... *)
Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

(** Alternatively, we can declare an argument to be implicit while
    defining the function itself, by surrounding the argument in curly
    braces.  For example: *)

Fixpoint length'' {X:Type} (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length'' t)
  end.

(** (Note that we didn't even have to provide a type argument to
    the recursive call to [length''].)  We will use this style
    whenever possible, although we will continue to use use explicit
    [Implicit Argument] declarations for [Inductive] constructors. *)

(** One small problem with declaring arguments [Implicit] is
    that, occasionally, Coq does not have enough local information to
    determine a type argument; in such cases, we need to tell Coq that
    we want to give the argument explicitly this time, even though
    we've globally declared it to be [Implicit].  For example, if we
    write: *)

(* Definition mynil := nil. *)

(** If we uncomment this definition, Coq will give us an error,
    because it doesn't know what type argument to supply to [nil].  We
    can help it by providing an explicit type declaration (so that Coq
    has more information available when it gets to the "application"
    of [nil]): *)

Definition mynil : list nat := nil.

(** Alternatively, we can force the implicit arguments to be explicit by
   prefixing the function name with [@]. *)

Check @nil.

Definition mynil' := @nil nat.

(** Using argument synthesis and implicit arguments, we can
    define convenient notation for lists, as before.  Since we have
    made the constructor type arguments implicit, Coq will know to
    automatically infer these when we use the notations. *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(** Now lists can be written just the way we'd hope: *)

Definition list123''' := [1, 2, 3].

(* ###################################################### *)
(** *** Exercises: Polymorphic Lists *)

(** **** Exercise: 2 stars, optional (poly_exercises) *)
(** Here are a few simple exercises, just like ones in the [Lists]
    chapter, for practice with polymorphism.  Fill in the definitions
    and complete the proofs below. *)

Fixpoint repeat (X : Type) (n : X) (count : nat) : list X :=
  match count with
  | O        => nil
  | S count' => n :: (repeat _ n count')
  end.

Example test_repeat1:
  repeat bool true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.

Theorem nil_app : forall X:Type, forall l:list X,
  app [] l = l.
Proof.
  reflexivity. Qed.

Theorem rev_snoc : forall X : Type,
                     forall v : X,
                     forall s : list X,
  rev (snoc s v) = v :: (rev s).
Proof.
  intros X v s. induction s.
  Case "s = nil".
    reflexivity.
  Case "s = cons".
    simpl. rewrite -> IHs. reflexivity.  Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l. induction l as [| x l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> rev_snoc. rewrite -> IHl'. reflexivity.  Qed.

Theorem snoc_with_append : forall X : Type,
                         forall l1 l2 : list X,
                         forall v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros X l1 l2 v. induction l1 as [| x l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.
(** [] *)

(* ###################################################### *)
(** ** Polymorphic Pairs *)

(** Following the same pattern, the type definition we gave in
    the last chapter for pairs of numbers can be generalized to
    _polymorphic pairs_ (or _products_): *)

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Implicit Arguments pair [[X] [Y]].

(** As with lists, we make the type arguments implicit and define the
    familiar concrete notation. *)

Notation "( x , y )" := (pair x y).

(** We can also use the [Notation] mechanism to define the standard
    notation for pair _types_: *)

Notation "X * Y" := (prod X Y) : type_scope.

(** (The annotation [: type_scope] tells Coq that this abbreviation
    should be used when parsing types.  This avoids a clash with the
    multiplication symbol.) *)

(** A note of caution: it is easy at first to get [(x,y)] and
    [X*Y] confused.  Remember that [(x,y)] is a _value_ built from two
    other values; [X*Y] is a _type_ built from two other types.  If
    [x] has type [X] and [y] has type [Y], then [(x,y)] has type
    [X*Y]. *)

(** The first and second projection functions now look pretty
    much as they would in any functional programming language. *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with (x,y) => y end.

(** The following function takes two lists and combines them
    into a list of pairs.  In many functional programming languages,
    it is called [zip].  We call it [combine] for consistency with
    Coq's standard library. *)
(** Note that the pair notation can be used both in expressions and in
    patterns... *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match (lx,ly) with
  | ([],_) => []
  | (_,[]) => []
  | (x::tx, y::ty) => (x,y) :: (combine tx ty)
  end.

(** Indeed, when no ambiguity results, we can even drop the enclosing
    parens: *)

Fixpoint combine' {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx,ly with
  | [],_ => []
  | _,[] => []
  | x::tx, y::ty => (x,y) :: (combine' tx ty)
  end.



(** **** Exercise: 1 star, optional (combine_checks) *)
(** Try answering the following questions on paper and
    checking your answers in coq:
    - What is the type of [combine] (i.e., what does [Check
      @combine] print?)
    - What does
        Eval simpl in (combine [1,2] [false,false,true,true]).
      print?   []
*)

Check @combine.

Eval simpl in (combine [1,2] [false,false,true,true]).

(** **** Exercise: 2 stars, recommended (split) *)
(** The function [split] is the right inverse of combine: it takes a
    list of pairs and returns a pair of lists.  In many functional
    programing languages, this function is called [unzip].

    Uncomment the material below and fill in the definition of
    [split].  Make sure it passes the given unit tests. *)

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
  match l with
  | nil          => ([], [])
  | (x, y) :: l' => (x :: fst (split l'), y :: snd (split l'))
  end.

Example test_split:
  split [(1,false),(2,false)] = ([1,2],[false,false]).
Proof. reflexivity.  Qed.

(** (If you're reading the HTML version of this file, note that
    there's an unresolved typesetting problem in the example: several
    square brackets are missing.  Refer to the .v file for the correct
    version. *)
(** [] *)

(* ###################################################### *)
(** ** Polymorphic Options *)

(** One last polymorphic type for now: _polymorphic options_.
    The type declaration generalizes the one for [natoption] in the
    previous chapter: *)

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Implicit Arguments Some [[X]].
Implicit Arguments None [[X]].

(** We can now rewrite the [index] function so that it works
    with any type of lists. *)

Fixpoint index {X : Type} (n : nat)
               (l : list X) : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Example test_index1 :    index 0 [4,5,6,7]  = Some 4.
Proof. reflexivity.  Qed.
Example test_index2 :    index  1 [[1],[2]]  = Some [2].
Proof. reflexivity.  Qed.
Example test_index3 :    index  2 [true]  = None.
Proof. reflexivity.  Qed.

(** **** Exercise: 1 star, optional (hd_opt_poly) *)
(** Complete the definition of a polymorphic version of the
    [hd_opt] function from the last chapter. Be sure that it
    passes the unit tests below. *)

Definition hd_opt {X : Type} (l : list X)  : option X :=
  match l with
  | nil     => None
  | x :: l' => Some x
  end.

(** Once again, to force the implicit arguments to be explicit,
    we can use [@] before the name of the function. *)

Check @hd_opt.

Example test_hd_opt1 :  hd_opt [1,2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt2 :   hd_opt  [[1],[2]]  = Some [1].
Proof. reflexivity. Qed.
(** [] *)

(* ###################################################### *)
(** * Functions as Data *)

(* ###################################################### *)
(** ** Higher-Order Functions *)

(** Like many other modern programming languages -- including
    all _functional languages_ (ML, Haskell, Scheme, etc.) -- Coq
    treats functions as first-class citizens, allowing functions to be
    passed as arguments to other functions, returned as results,
    stored in data structures, etc.

    Functions that manipulate other functions are often called
    _higher-order_ functions.  Here's a simple one: *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

(** The argument [f] here is itself a function (from [X] to
    [X]); the body of [doit3times] applies [f] three times to some
    value [n]. *)

Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity.  Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(** ** Partial Application *)

(** In fact, the multiple-argument functions we have already
    seen are also examples of passing functions as data.  To see why,
    recall the type of [plus]. *)

Check plus.
(* ==> nat -> nat -> nat *)

(** Each [->] in this expression is actually a _binary_ operator
    on types.  (This is the same as saying that Coq primitively
    supports only one-argument functions -- do you see why?)  This
    operator is _right-associative_, so the type of [plus] is really a
    shorthand for [nat -> (nat -> nat)] -- i.e., it can be read as
    saying that "[plus] is a one-argument function that takes a [nat]
    and returns a one-argument function that takes another [nat] and
    returns a [nat]."  In the examples above, we have always applied
    [plus] to both of its arguments at once, but if we like we can
    supply just the first.  This is called _partial application_. *)

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity.  Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity.  Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(** ** Digression: Currying *)

(** **** Exercise: 2 stars, optional (currying) *)
(** In Coq, a function [f : A -> B -> C] really has the type [A
    -> (B -> C)].  That is, if you give [f] a value of type [A], it
    will give you function [f' : B -> C].  If you then give [f'] a
    value of type [B], it will return a value of type [C].  This
    allows for partial application, as in [plus3].  Processing a list
    of arguments with functions that return functions is called
    _currying_, in honor of the logician Haskell Curry.

    Conversely, we can reinterpret the type [A -> B -> C] as [(A *
    B) -> C].  This is called _uncurrying_.  With an uncurried binary
    function, both arguments must be given at once as a pair; there is
    no partial application. *)

(** We can define currying as follows: *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(** As an exercise, define its inverse, [prod_uncurry].  Then prove
    the theorems below to show that the two are inverses. *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

(** (Thought exercise: before running these commands, can you
    calculate the types of [prod_curry] and [prod_uncurry]?) *)

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  reflexivity.  Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                               (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p. destruct p. reflexivity.  Qed.
(** [] *)

(* ###################################################### *)
(** ** Filter *)

(** Here is a useful higher-order function, which takes a list
    of [X]s and a _predicate_ on [X] (a function from [X] to [bool])
    and "filters" the list, returning a new list containing just those
    elements for which the predicate returns [true]. *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

(** For example, if we apply [filter] to the predicate [evenb]
    and a list of numbers [l], it returns a list containing just the
    even members of [l]. *)

Example test_filter1: filter evenb [1,2,3,4] = [2,4].
Proof. reflexivity.  Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
           [ [1, 2], [3], [4], [5,6,7], [], [8] ]
  = [ [3], [4], [8] ].
Proof. reflexivity.  Qed.

(** We can use [filter] to give a concise version of the
    [countoddmembers] function from the [Lists] chapter. *)

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1:   countoddmembers' [1,0,3,1,4,5] = 4.
Proof. reflexivity.  Qed.
Example test_countoddmembers'2:   countoddmembers' [0,2,4] = 0.
Proof. reflexivity.  Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. reflexivity.  Qed.

(* ###################################################### *)
(** ** Anonymous Functions *)

(** It is a little annoying to be forced to define the function
    [length_is_1] and give it a name just to be able to pass it as an
    argument to [filter], since we will probably never use it again.
    Moreover, this is not an isolated example.  When using
    higher-order functions, we often want to pass as arguments
    "one-off" functions that we will never use again; having to give
    each of these functions a name would be tedious.

    Fortunately, there is a better way. It is also possible to
    construct a function "on the fly" without declaring it at the top
    level or giving it a name; this is analogous to the notation we've
    been using for writing down constant lists, natural numbers, and
    so on. *)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity.  Qed.

(** Here is the motivating example from before, rewritten to use
    an anonymous function. *)

Example test_filter2':
    filter (fun l => beq_nat (length l) 1)
           [ [1, 2], [3], [4], [5,6,7], [], [8] ]
  = [ [3], [4], [8] ].
Proof. reflexivity.  Qed.

(** **** Exercise: 2 stars (filter_even_gt7) *)

(** Use [filter] (instead of [Fixpoint]) to write a Coq function
    [filter_even_gt7] which takes a list of natural numbers as input
    and keeps only those numbers which are even and greater than 7. *)

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (evenb n) (negb (ble_nat n 7))) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5,2,6,19,129] = [].
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 3 stars (partition) *)
(** Use [filter] to write a Coq function [partition]:
  partition : forall X : Type,
              (X -> bool) -> list X -> list X * list X
   Given a set [X], a test function of type [X -> bool] and a [list
   X], [partition] should return a pair of lists.  The first member of
   the pair is the sublist of the original list containing the
   elements that satisfy the test, and the second is the sublist
   containing those that fail the test.  The order of elements in the
   two sublists should be the same as their order in the original
   list.
*)

Definition partition {X : Type} (test : X -> bool) (l : list X)
                     : list X * list X :=
  (filter test l, filter (fun x => negb (test x)) l).

Example test_partition1: partition oddb [1,2,3,4,5] = ([1,3,5], [2,4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5,9,0] = ([], [5,9,0]).
Proof. reflexivity. Qed.
(** [] *)

(* ###################################################### *)
(** ** Map *)

(** Another handy higher-order function is called [map]. *)

Fixpoint map {X Y:Type} (f:X->Y) (l:list X)
             : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(** It takes a function [f] and a list [ l = [n1, n2, n3, ...] ]
    and returns the list [ [f n1, f n2, f n3,...] ], where [f] has
    been applied to each element of [l] in turn.  For example: *)

Example test_map1: map (plus 3) [2,0,2] = [5,3,5].
Proof. reflexivity.  Qed.

(** The element types of the input and output lists need not be
    the same ([map] takes _two_ type arguments, [X] and [Y]).  This
    version of [map] can thus be applied to a list of numbers and a
    function from numbers to booleans to yield a list of booleans: *)

Example test_map2: map oddb [2,1,2,5] = [false,true,false,true].
Proof. reflexivity.  Qed.

(** It can even be applied to a list of numbers and
    a function from numbers to _lists_ of booleans to
    yield a list of lists of booleans: *)

Example test_map3:
    map (fun n => [evenb n,oddb n]) [2,1,2,5]
  = [[true,false],[false,true],[true,false],[false,true]].
Proof. reflexivity.  Qed.


(** **** Exercise: 3 stars, optional (map_rev) *)
(** Show that [map] and [rev] commute.  You may need to define an
    auxiliary lemma. *)

Theorem map_snoc: forall (X Y : Type) (f : X -> Y) (x : X) (l : list X),
  map f (snoc l x) = snoc (map f l) (f x).
Proof.
  intros X Y f x l. induction l as [| y l' ].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> IHl'. reflexivity.  Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l. induction l as [| x l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> map_snoc. rewrite -> IHl'. reflexivity.  Qed.
(** [] *)

(** **** Exercise: 2 stars, recommended (flat_map) *)
(** The function [map] maps a [list X] to a [list Y] using a function
    of type [X -> Y].  We can define a similar function, [flat_map],
    which maps a [list X] to a [list Y] using a function [f] of type
    [X -> list Y].  Your definition should work by 'flattening' the
    results of [f], like so:
        flat_map (fun n => [n,n+1,n+2]) [1,5,10]
      = [1, 2, 3, 5, 6, 7, 10, 11, 12].
*)

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X)
                   : (list Y) :=
  match l with
  | []      => []
  | x :: l' => (f x) ++ (flat_map f l')
  end.

Example test_flat_map1:
  flat_map (fun n => [n,n,n]) [1,5,4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4].
Proof. reflexivity. Qed.
(** [] *)

(** Lists are not the only inductive type that we can write a
    [map] function for.  Here is the definition of [map] for the
    [option] type: *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(** **** Exercise: 2 stars, optional (implicit_args) *)
(** The definitions and uses of [filter] and [map] use implicit
    arguments in many places.  Replace the curly braces around the
    implicit arguments with parentheses, and then fill in explicit
    type parameters where necessary and use Coq to check that you've
    done so correctly.  This exercise is not to be turned in; it is
    probably easiest to do it on a _copy_ of this file that you can
    throw away afterwards.  [] *)

(* ###################################################### *)
(** ** Fold *)

(** An even more powerful higher-order function is called
    [fold].  This function is the inspiration for the "[reduce]"
    operation that lies at the heart of Google's map/reduce
    distributed programming framework. *)

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(** Intuitively, the behavior of the [fold] operation is to
    insert a given binary operator [f] between every pair of elements
    in a given list.  For example, [ fold plus [1,2,3,4] ] intuitively
    means [1+2+3+4].  To make this precise, we also need a "starting
    element" that serves as the initial second input to [f].  So, for
    example,
   fold plus [1,2,3,4] 0
    yields
   1 + (2 + (3 + (4 + 0))).
    Here are some more examples:
*)

Check (fold plus).
Eval simpl in (fold plus [1,2,3,4] 0).

Example fold_example1 : fold mult [1,2,3,4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 : fold andb [true,true,false,true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 : fold app  [[1],[],[2,3],[4]] [] = [1,2,3,4].
Proof. reflexivity. Qed.

(** **** Exercise: 1 star, optional (fold_types_different) *)
(** Observe that the type of [fold] is parameterized by _two_ type
    variables, [X] and [Y], and the parameter [f] is a binary operator
    that takes an [X] and a [Y] and returns a [Y].  Can you think of a
    situation where it would be useful for [X] and [Y] to be
    different? *)

(* ###################################################### *)
(** ** Functions For Constructing Functions *)

(** Most of the higher-order functions we have talked about so
    far take functions as _arguments_.  Now let's look at some
    examples involving _returning_ functions as the results of other
    functions.

    To begin, here is a function that takes a value [x] (drawn from
    some type [X]) and returns a function from [nat] to [X] that
    yields [x] whenever it is called, ignoring its [nat] argument. *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(** Similarly, but a bit more interestingly, here is a function
    that takes a function [f] from numbers to some type [X], a number
    [k], and a value [x], and constructs a function that behaves
    exactly like [f] except that, when called with the argument [k],
    it returns [x]. *)

Definition override {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if beq_nat k k' then x else f k'.

(** For example, we can apply [override] twice to obtain a
    function from numbers to booleans that returns [false] on [1] and
    [3] and returns [true] on all other arguments. *)

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

(** **** Exercise: 1 star (override_example) *)
(** Before starting to work on the following proof, make sure you
    understand exactly what the theorem is saying and can paraphrase
    it in your own words.  The proof itself is straightforward. *)

Theorem override_example : forall (b:bool),
  (override (constfun b) 3 true) 2 = b.
Proof.
  reflexivity.  Qed.
(** [] *)

(** We'll use function overriding heavily in parts of the rest of the
    course, and we will end up needing to know quite a bit about its
    properties.  To prove these properties, though, we need to know
    about a few more of Coq's tactics; developing these is the main
    topic of the rest of the chapter. *)

(* ##################################################### *)
(* ##################################################### *)
(** * Optional Material *)
(** ** Non-Uniform Inductive Families (GADTs) *)

(** _This section needs more text_! *)

(** Recall the definition of lists of booleans:
Inductive boollist : Type :=
  boolnil  : boollist
| boolcons : bool -> boollist -> boollist.
*)

(** We saw how it could be generalized to "polymorphic lists" with
    elements of an arbitrary type [X].  Here's another way of
    generalizing it: an inductive family of "length-indexed" lists of
    booleans: *)

Inductive boolllist : nat -> Type :=
  boollnil  : boolllist O
| boollcons : forall n, bool -> boolllist n -> boolllist (S n).

Implicit Arguments boollcons [[n]].

Check (boollcons true (boollcons false (boollcons true boollnil))).

Fixpoint blapp {n1} (l1: boolllist n1)
               {n2} (l2: boolllist n2)
             : boolllist (n1 + n2) :=
  match l1 with
  | boollnil        => l2
  | boollcons _ h t => boollcons h (blapp t l2)
  end.

(** Of course, these generalizions can be combined.  Here's the
    length-indexed polymorphic version: *)

Inductive llist (X:Type) : nat -> Type :=
  lnil  : llist X O
| lcons : forall n, X -> llist X n -> llist X (S n).

Implicit Arguments lnil [[X]].
Implicit Arguments lcons [[X] [n]].

Check (lcons true (lcons false (lcons true lnil))).

Fixpoint lapp (X:Type)
              {n1} (l1: llist X n1)
              {n2} (l2: llist X n2)
            : llist X (n1 + n2) :=
  match l1 with
  | lnil        => l2
  | lcons _ h t => lcons h (lapp X t l2)
  end.

(* ###################################################### *)
(** * More About Coq *)


(* ###################################################### *)
(** ** The [apply] Tactic *)

(** We often encounter situations where the goal to be proved is
    exactly the same as some hypothesis in the context or some
    previously proved lemma. *)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n,o] = [n,p] ->
     [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  (* At this point, we could finish with "[rewrite -> eq2. reflexivity.]"
     as we have done several times above. But we can achieve the
     same effect in a single step by using the [apply] tactic instead: *)
  apply eq2.  Qed.

(** The [apply] tactic also works with _conditional_ hypotheses
    and lemmas: if the statement being applied is an implication, then
    the premises of this implication will be added to the list of
    subgoals needing to be proved. *)

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q,o] = [r,p]) ->
     [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** You may find it instructive to experiment with this proof
    and see if there is a way to complete it using just [rewrite]
    instead of [apply]. *)

(** Typically, when we use [apply H], the statement [H] will
    begin with a [forall] binding some _universal variables_.  When
    Coq matches the current goal against the conclusion of [H], it
    will try to find appropriate values for these variables.  For
    example, when we do [apply eq2] in the following proof, the
    universal variable [q] in [eq2] gets instantiated with [n] and [r]
    gets instantiated with [m]. *)

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** **** Exercise: 2 stars, optional (silly_ex) *)
(** Complete the following proof without using [simpl]. *)

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros eq1 eq2. apply eq1. apply eq2.  Qed.
(** [] *)

(** To use the [apply] tactic, the (conclusion of the) fact
    being applied must match the goal _exactly_ -- for example, [apply]
    will not work if the left and right sides of the equality are
    swapped. *)

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
  (* Here we cannot use [apply] directly *)
Admitted.

(** In this case we can use the [symmetry] tactic, which
    switches the left and right sides of an equality in the goal. *)

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl. (* Actually, this [simpl] is unnecessary, since
            [apply] will do a [simpl] step first. *)
  apply H.  Qed.

(** **** Exercise: 3 stars, recommended (apply_exercise1) *)

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  (* Hint: you can use [apply] with previously defined lemmas, not
     just hypotheses in the context.  Remember that [SearchAbout] is
     your friend. *)
  intros l l' H. rewrite -> H. symmetry. apply rev_involutive.  Qed.
(** [] *)

(** **** Exercise: 1 star (apply_rewrite) *)
(** Briefly explain the difference between the tactics [apply] and
    [rewrite].  Are there situations where both can usefully be
    applied?

  (* FILL IN HERE *)
*)
(** [] *)

(* ###################################################### *)
(** ** The [unfold] Tactic *)

(** Sometimes, a proof will get stuck because Coq doesn't
    automatically expand a function call into its definition.  (This
    is a feature, not a bug: if Coq automatically expanded everything
    possible, our proof goals would quickly become enormous -- hard to
    read and slow for Coq to manipulate!) *)

Theorem unfold_example_bad : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  (* At this point, we'd like to do [rewrite -> H], since
     [plus3 n] is definitionally equal to [3 + n].  However,
     Coq doesn't automatically expand [plus3 n] to its
     definition. *)
  Admitted.

(** The [unfold] tactic can be used to explicitly replace a
    defined name by the right-hand side of its definition.  *)

Theorem unfold_example : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  unfold plus3.
  rewrite -> H.
  reflexivity.  Qed.

(** Now we can prove a first property of [override]: If we
    override a function at some argument [k] and then look up [k], we
    get back the overridden value. *)

Theorem override_eq : forall {X:Type} x k (f:nat->X),
  (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity.  Qed.

(** This proof was straightforward, but note that it requires
    [unfold] to expand the definition of [override]. *)

(** **** Exercise: 2 stars (override_neq) *)
Theorem override_neq : forall {X:Type} x1 x2 k1 k2 (f : nat->X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof.
  intros X x1 x2 k1 k2 f eq1 eq2.
  unfold override. rewrite -> eq2. apply eq1.  Qed.
(** [] *)

(** As the inverse of [unfold], Coq also provides a tactic
    [fold], which can be used to "unexpand" a definition.  It is used
    much less often. *)

(* ###################################################### *)
(** ** Inversion *)

(** Recall the definition of natural numbers:
     Inductive nat : Type :=
       | O : nat
       | S : nat -> nat.
    It is clear from this definition that every number has one of two
    forms: either it is the constructor [O] or it is built by applying
    the constructor [S] to another number.  But there is more here than
    meets the eye: implicit in the definition (and in our informal
    understanding of how datatype declarations work in other
    programming languages) are two other facts:

    - The constructor [S] is _injective_.  That is, the only way we can
      have [S n = S m] is if [n = m].

    - The constructors [O] and [S] are _disjoint_.  That is, [O] is not
      equal to [S n] for any [n]. *)

(** Similar principles apply to all inductively defined types: all
    constructors are injective, and the values built from distinct
    constructors are never equal.  For lists, the [cons] constructor is
    injective and [nil] is different from every non-empty list.  For
    booleans, [true] and [false] are unequal.  (Since neither [true]
    nor [false] take any arguments, their injectivity is not an issue.) *)

(** Coq provides a tactic, called [inversion], that allows us to
    exploit these principles in making proofs.

    The [inversion] tactic is used like this.  Suppose [H] is a
    hypothesis in the context (or a previously proven lemma) of the
    form
      c a1 a2 ... an = d b1 b2 ... bm
    for some constructors [c] and [d] and arguments [a1 ... an] and
    [b1 ... bm].  Then [inversion H] instructs Coq to "invert" this
    equality to extract the information it contains about these terms:

    - If [c] and [d] are the same constructor, then we know, by the
      injectivity of this constructor, that [a1 = b1], [a2 = b2],
      etc.; [inversion H] adds these facts to the context, and tries
      to use them to rewrite the goal.

    - If [c] and [d] are different constructors, then the hypothesis
      [H] is contradictory.  That is, a false assumption has crept
      into the context, and this means that any goal whatsoever is
      provable!  In this case, [inversion H] marks the current goal as
      completed and pops it off the goal stack. *)

(** The [inversion] tactic is probably easier to understand by
    seeing it in action than from general descriptions like the above.
    Below you will find example theorems that demonstrate the use of
    [inversion] and exercises to test your understanding. *)

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity.  Qed.

Theorem silly4 : forall (n m : nat),
     [n] = [m] ->
     n = m.
Proof.
  intros n o eq. inversion eq. reflexivity.  Qed.

(** As a convenience, the [inversion] tactic can also
    destruct equalities between complex values, binding
    multiple variables as it goes. *)

Theorem silly5 : forall (n m o : nat),
     [n,m] = [o,o] ->
     [n] = [m].
Proof.
  intros n m o eq. inversion eq. reflexivity. Qed.

(** **** Exercise: 1 star (sillyex1) *)
Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  intros X x y z l j eq1 eq2. inversion eq2. reflexivity.  Qed.
(** [] *)

Theorem silly6 : forall (n : nat),
     S n = O ->
     2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem silly7 : forall (n m : nat),
     false = true ->
     [n] = [m].
Proof.
  intros n m contra. inversion contra.  Qed.

(** **** Exercise: 1 star (sillyex2) *)
Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  intros X x y z l j eq1 eq2. inversion eq1.  Qed.
(** [] *)

(** While the injectivity of constructors allows us to reason
    [forall (n m : nat), S n = S m -> n = m], the reverse direction of
    the implication, provable by standard equational reasoning, is a
    useful fact to record for cases we will see several times. *)

Lemma eq_remove_S : forall n m,
  n = m -> S n = S m.
Proof. intros n m eq. rewrite -> eq. reflexivity. Qed.

(** Here's another illustration of [inversion].  This is a slightly
    roundabout way of stating a fact that we have already proved
    above.  The extra equalities force us to do a little more
    equational reasoning and exercise some of the tactics we've seen
    recently. *)

Theorem length_snoc' : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  intros X v l. induction l as [| v' l'].
  Case "l = []". intros n eq. rewrite <- eq. reflexivity.
  Case "l = v' :: l'". intros n eq. simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply eq_remove_S. apply IHl'. inversion eq. reflexivity. Qed.

(* ###################################################### *)
(** ** Varying the Induction Hypothesis *)

(** Here is a more realistic use of inversion to prove a
    property that is useful in many places later on... *)

Theorem beq_nat_eq_FAILED : forall n m,
  true = beq_nat n m -> n = m.
Proof.
  intros n m H. induction n as [| n'].
  Case "n = 0".
    destruct m as [| m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". simpl in H. inversion H.
  Case "n = S n'".
    destruct m as [| m'].
    SCase "m = 0". simpl in H. inversion H.
    SCase "m = S m'".
      apply eq_remove_S.
      (* stuck here because the induction hypothesis
         talks about an extremely specific m *)
      Admitted.

(** The inductive proof above fails because we've set up things so
    that the induction hypothesis (in the second subgoal generated by
    the [induction] tactic) is

       [ true = beq_nat n' m -> n' = m ].

     This hypothesis makes a statement about [n'] together with the
     _particular_ natural number [m] -- that is, the number [m], which
     was introduced into the context by the [intros] at the top of the
     proof, is "held constant" in the induction hypothesis.  This
     induction hypothesis is not strong enough to make the induction
     step of the proof go through.

     If we set up the proof slightly differently by introducing just
     [n] into the context at the top, then we get an induction
     hypothesis that makes a stronger claim:

      [ forall m : nat, true = beq_nat n' m -> n' = m ]

     Setting up the induction hypothesis this way makes the proof of
     [beq_nat_eq] go through: *)

Theorem beq_nat_eq : forall n m,
  true = beq_nat n m -> n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    intros m. destruct m as [| m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". simpl. intros contra. inversion contra.
  Case "n = S n'".
    intros m. destruct m as [| m'].
    SCase "m = 0". simpl. intros contra. inversion contra.
    SCase "m = S m'". simpl. intros H.
      apply eq_remove_S. apply IHn'. apply H. Qed.

(** Similar issues will come up in _many_ of the proofs below.  If you
    ever find yourself in a situation where the induction hypothesis
    is insufficient to establish the goal, consider going back and
    doing fewer [intros] to make the IH stronger. *)

(** **** Exercise: 2 stars (beq_nat_eq_informal) *)
(** Give an informal proof of [beq_nat_eq]. *)
(** We need to show:

  n = m if beq_nat n m = true

  By induction on n.

  First, we need to show:

  0 = m if beq_nat 0 m = true.

  We need to consider two cases:

  - m = 0, then 0 = 0;

  - m = S m', then 0 = S m' if beq_nat 0 (S m') = true, but by
    definition of the beq_nat we have contradiction false = true, a
    false assumption has crept into the context, and this means that
    this goal is provable.

  Second, we nee to show:

  S n' = m if beq_nat (S n') m = true.

  We need to consider two cases:

  - m = 0, then S n' = 0 if beq_nat (S n') 0 = true, but by definition
    of beq_nat we have a contradiction;

  - m = S m', then S n' = S m' if beq_nat (S n') (S m') = true, by
    using the previously proved fact, that S n = S m -> n = m, we must
    prove that n' = m' wich is obvious from inductive assumption and
    initial premise.
*)
(** [] *)

(** **** Exercise: 3 stars (beq_nat_eq') *)
(** We can also prove beq_nat_eq by induction on [m], though we have
    to be a little careful about which order we introduce the
    variables, so that we get a general enough induction hypothesis --
    this is done for you below.  Finish the following proof.  To get
    maximum benefit from the exercise, try first to do it without
    looking back at the one above. *)

Theorem beq_nat_eq' : forall m n,
  beq_nat n m = true -> n = m.
Proof.
  intros m. induction m as [| m'].
  Case "m = O".
    intros n H. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion H.
  Case "m = S m'".
    intros n H. destruct n as [| n'].
    SCase "n = O". inversion H.
    SCase "n = S n'".
      apply eq_remove_S. apply IHm'. simpl in H. apply H.  Qed.
(** [] *)


(* ###################################################### *)
(** *** Practice Session *)

(** **** Exercise: 2 stars, optional (practice) *)
(** Some nontrivial but not-too-complicated proofs to work together in
    class, and some for you to work as exercises.  Some of the
    exercises may involve applying lemmas from earlier lectures or
    homeworks. *)


Theorem beq_nat_0_l : forall n,
  true = beq_nat 0 n -> 0 = n.
Proof.
  apply beq_nat_eq.  Qed.

Theorem beq_nat_0_r : forall n,
  true = beq_nat 0 n -> 0 = n.
Proof.
  apply beq_nat_eq.  Qed.
(** [] *)

(** **** Exercise: 3 stars (apply_exercise2) *)
(** In the following proof opening, notice that we don't introduce [m]
    before performing induction.  This leaves it general, so that the
    IH doesn't specify a particular [m], but lets us pick.  Finish the
    proof. *)

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n. induction n as [| n'].
  Case "n = O".
    intros m. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". reflexivity.
  Case "n = S n'".
    intros m. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". simpl. apply IHn'.  Qed.
(** [] *)

(** **** Exercise: 3 stars (beq_nat_sym_informal) *)
(** Provide an informal proof of this lemma that corresponds
    to your formal proof above:

   Theorem: For any [nat]s [n] [m], [beq_nat n m = beq_nat m n].

   Proof:
   (* FILL IN HERE *)
[]
 *)

(* ###################################################### *)
(** ** Using Tactics on Hypotheses *)

(** By default, most tactics work on the goal formula and leave
    the context unchanged.  However, most tactics also have a variant
    that performs a similar operation on a statement in the context.

    For example, the tactic [simpl in H] performs simplification in
    the hypothesis named [H] in the context. *)

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b  ->
     beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

(** Similarly, the tactic [apply L in H] matches some
    conditional statement [L] (of the form [L1 -> L2], say) against a
    hypothesis [H] in the context.  However, unlike ordinary
    [apply] (which rewrites a goal matching [L2] into a subgoal [L1]),
    [apply L in H] matches [H] against [L1] and, if successful,
    replaces it with [L2].

    In other words, [apply L in H] gives us a form of "forward
    reasoning" -- from [L1 -> L2] and a hypothesis matching [L1], it
    gives us a hypothesis matching [L2].  By contrast, [apply L] is
    "backward reasoning" -- it says that if we know [L1->L2] and we
    are trying to prove [L2], it suffices to prove [L1].

    Here is a variant of a proof from above, using forward reasoning
    throughout instead of backward reasoning. *)

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5  ->
     true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H.  Qed.

(** Forward reasoning starts from what is _given_ (premises,
    previously proven theorems) and iteratively draws conclusions from
    them until the goal is reached.  Backward reasoning starts from
    the _goal_, and iteratively reasons about what would imply the
    goal, until premises or previously proven theorems are reached.
    If you've seen informal proofs before (for example, in a math or
    computer science class), they probably used forward reasoning.  In
    general, Coq tends to favor backward reasoning, but in some
    situations the forward style can be easier to use or to think
    about.  *)

(** **** Exercise: 3 stars, recommended (plus_n_n_injective) *)
(** You can practice using the "in" variants in this exercise. *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
    (* Hint: use the plus_n_Sm lemma *)
  Case "n = O".
    intros m H. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion H.
  Case "n = S n'".
    intros m H. destruct m as [| m'].
    SCase "m = O". inversion H.
    SCase "m = S m'".
      rewrite <- plus_n_Sm in H.
      rewrite <- plus_n_Sm in H.
      inversion H.
      apply IHn' in H1.
      rewrite -> H1. reflexivity.  Qed.
(** [] *)

(* ###################################################### *)
(** ** Using [destruct] on Compound Expressions *)


(** We have seen many examples where the [destruct] tactic is
    used to perform case analysis of the value of some variable.  But
    sometimes we need to reason by cases on the result of some
    _expression_.  We can also do this with [destruct].

    Here are some examples: *)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
    Case "beq_nat n 3 = true". reflexivity.
    Case "beq_nat n 3 = false". destruct (beq_nat n 5).
      SCase "beq_nat n 5 = true". reflexivity.
      SCase "beq_nat n 5 = false". reflexivity.  Qed.

(** After unfolding [sillyfun] in the above proof, we find that
    we are stuck on [if (beq_nat n 3) then ... else ...].  Well,
    either [n] is equal to [3] or it isn't, so we use [destruct
    (beq_nat n 3)] to let us reason about the two cases. *)

(** **** Exercise: 1 star (override_shadow) *)
Theorem override_shadow : forall {X:Type} x1 x2 k1 k2 (f : nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f. unfold override. destruct (beq_nat k1 k2).
  Case "beq_nat k1 k2 = true". reflexivity.
  Case "beq_nat k1 k2 = false". reflexivity.  Qed.
(** [] *)

(** **** Exercise: 3 stars, recommended (combine_split) *)

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [| [x y] l'].
  Case "l = nil".
    intros l1 l2 H.
    simpl in H. inversion H. reflexivity.
  Case "l = cons".
    intros s1 s2 H. simpl in H.
    destruct (split l') as [l1' l2'].
    inversion H. simpl.
    assert (H': combine l1' l2' = l').
    SCase "Proof of assertion". apply IHl'. reflexivity.
    rewrite -> H'. reflexivity.  Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (split_combine) *)
(** Thought exercise: We have just proven that for all lists of pairs,
    [combine] is the inverse of [split].  How would you state the
    theorem showing that [split] is the inverse of [combine]?

    Hint: what property do you need of [l1] and [l2] for [split]
    [combine l1 l2 = (l1,l2)] to be true?

    State this theorem in Coq, and prove it. (Be sure to leave your
    induction hypothesis general by not doing [intros] on more things
    than necessary.) *)

Theorem split_combine: forall (X Y : Type) (l1 : list X) (l2 : list Y),
  length l1 = length l2 ->
  split (combine l1 l2) = (l1, l2).
Proof.
  intros X Y l1. induction l1.
  Case "l1 = nil".
    destruct l2 as [| y l2'].
    SCase "l2 = nil". reflexivity.
    SCase "l2 = cons". intros contra. inversion contra.
  Case "l1 = cons".
    destruct l2 as [| y l2'].
    SCase "l2 = nil". intros contra. inversion contra.
    SCase "l2 = cons".
      simpl. intros H. inversion H.
      apply IHl1 in H1. rewrite -> H1. reflexivity.  Qed.
(** [] *)

(* ###################################################### *)
(** ** The [remember] Tactic *)

(** (Note: the [remember] tactic is not strictly needed until a
    bit later, so if necessary this section can be skipped and
    returned to when needed.) *)

(** We have seen how the [destruct] tactic can be used to
    perform case analysis of the results of arbitrary computations.
    If [e] is an expression whose type is some inductively defined
    type [T], then, for each constructor [c] of [T], [destruct e]
    generates a subgoal in which all occurrences of [e] (in the goal
    and in the context) are replaced by [c].

    Sometimes, however, this substitution process loses information
    that we need in order to complete the proof.  For example, suppose
    we define a function [sillyfun1] like this: *)

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

(** And suppose that we want to convince Coq of the rather
    obvious observation that [sillyfun1 n] yields [true] only when [n]
    is odd.  By analogy with the proofs we did with [sillyfun] above,
    it is natural to start the proof like this: *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  (* stuck... *)
Admitted.

(** We get stuck at this point because the context does not
    contain enough information to prove the goal!  The problem is that
    the substitution peformed by [destruct] is too brutal -- it threw
    away every occurrence of [beq_nat n 3], but we need to keep at
    least one of these because we need to be able to reason that
    since, in this branch of the case analysis, [beq_nat n 3 = true],
    it must be that [n = 3], from which it follows that [n] is odd.

    What we would really like is not to use [destruct] directly on
    [beq_nat n 3] and substitute away all occurrences of this
    expression, but rather to use [destruct] on something else that is
    _equal_ to [beq_nat n 3].  For example, if we had a variable that
    we knew was equal to [beq_nat n 3], we could [destruct] this
    variable instead.

    The [remember] tactic allows us to introduce such a variable. *)

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
   remember (beq_nat n 3) as e3.
   (* At this point, the context has been enriched with a new
      variable [e3] and an assumption that [e3 = beq_nat n 3].
      Now if we do [destruct e3]... *)
   destruct e3.
   (* ... the variable [e3] gets substituted away (it
     disappears completely) and we are left with the same
      state as at the point where we got stuck above, except
      that the context still contains the extra equality
      assumption -- now with [true] substituted for [e3] --
      which is exactly what we need to make progress. *)
     Case "e3 = true". apply beq_nat_eq in Heqe3.
       rewrite -> Heqe3. reflexivity.
     Case "e3 = false".
      (* When we come to the second equality test in the
        body of the function we are reasoning about, we can
         use [remember] again in the same way, allowing us
         to finish the proof. *)
       remember (beq_nat n 5) as e5. destruct e5.
         SCase "e5 = true".
           apply beq_nat_eq in Heqe5.
           rewrite -> Heqe5. reflexivity.
         SCase "e5 = false". inversion eq.  Qed.

(** **** Exercise: 2 stars (override_same) *)
Theorem override_same : forall {X:Type} x1 k1 k2 (f : nat->X),
  f k1 = x1 ->
  (override f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f eq.
  unfold override. remember (beq_nat k1 k2) as e.
  destruct e.
  Case "e = true".
    apply beq_nat_eq in Heqe. rewrite <- Heqe.
    symmetry. apply eq.
  Case "e = false".
    reflexivity.  Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (filter_exercise) *)
(** This one is a bit challenging.  Be sure your initial [intros] go
    only up through the parameter on which you want to do
    induction! *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X test x l lf. induction l as [| y l'].
  Case "l = nil".
    intros contra. inversion contra.
  Case "l = cons".
    simpl. remember (test y) as ty.
    destruct ty.
    SCase "ty = true".
      intros H. inversion H.
      rewrite <- H1. symmetry. apply Heqty.
    SCase "ty = false". apply IHl'.  Qed.
(** [] *)

(* ###################################################### *)
(** ** The [apply ... with ...] Tactic *)

(** The following silly example uses two rewrites in a row to
    get from [[a,b]] to [[e,f]]. *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a,b] = [c,d] ->
     [c,d] = [e,f] ->
     [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

(** Since this is a common pattern, we might
    abstract it out as a lemma recording once and for all
    the fact that equality is transitive. *)

Theorem trans_eq : forall {X:Type} (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.

(** Now, we should be able to use [trans_eq] to
    prove the above example.  However, to do this we need
    a slight refinement of the [apply] tactic. *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a,b] = [c,d] ->
     [c,d] = [e,f] ->
     [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2.
  (* If we simply tell Coq [apply trans_eq] at this point,
     it can tell (by matching the goal against the
     conclusion of the lemma) that it should instantiate [X]
     with [[nat]], [n] with [[a,b]], and [o] with [[e,f]].
     However, the matching process doesn't determine an
     instantiation for [m]: we have to supply one explicitly
     by adding [with (m:=[c,d])] to the invocation of
     [apply]. *)
  apply trans_eq with (m:=[c,d]). apply eq1. apply eq2.   Qed.

(**  Actually, we usually don't have to include the name [m]
    in the [with] clause; Coq is often smart enough to
    figure out which instantiation we're giving. We could
    instead write: apply trans_eq with [c,d]. *)

(** **** Exercise: 3 stars, recommended (apply_exercises) *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with m. apply eq2. apply eq1.  Qed.

Theorem beq_nat_trans : forall n m p,
  true = beq_nat n m ->
  true = beq_nat m p ->
  true = beq_nat n p.
Proof.
  intros n m p eq1 eq2.
  apply beq_nat_eq in eq1. rewrite -> eq1. apply eq2.  Qed.

Theorem override_permute : forall {X:Type} x1 x2 k1 k2 k3 (f : nat->X),
  false = beq_nat k2 k1 ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  intros X x1 x2 k1 k2 k3 f.
  unfold override. remember (beq_nat k1 k3) as e13.
  destruct e13.
  Case "e13 = true".
    remember (beq_nat k2 k3) as e23.
    destruct e23.
    SCase "e23 = true".
      apply beq_nat_trans with (p:=k1) in Heqe23.
      rewrite <- Heqe23.
      intros contra. inversion contra.
      SSCase "Proof for beq_nat_trans application".
        rewrite -> beq_nat_sym. apply Heqe13.
    SCase "e23 = false".
      reflexivity.
  Case "e13 = false".
    reflexivity.  Qed.

(** [] *)

(* ################################################################## *)
(** * Review *)

(** We've now seen a bunch of Coq's fundamental tactics -- enough to
    do pretty much everything we'll want for a while.  We'll introduce
    one or two more as we go along through the next few lectures, and
    later in the course we'll introduce some more powerful
    _automation_ tactics that make Coq do more of the low-level work
    in many cases.  But basically we've got what we need to get work
    done.

    Here are the ones we've seen:

      - [intros]:
        move hypotheses/variables from goal to context

      - [reflexivity]:
        finish the proof (when the goal looks like [e = e])

      - [apply]:
        prove goal using a hypothesis, lemma, or constructor

      - [apply... in H]:
        apply a hypothesis, lemma, or constructor to a hypothesis in
        the context (forward reasoning)

      - [apply... with...]:
        explicitly specify values for variables that cannot be
        determined by pattern matching

      - [simpl]:
        simplify computations in the goal

      - [simpl in H]:
        ... or a hypothesis

      - [rewrite]:
        use an equality hypothesis (or lemma) to rewrite the goal

      - [rewrite ... in H]:
        ... or a hypothesis

      - [symmetry]:
        changes a goal of the form [t=u] into [u=t]

      - [symmetry in H]:
        changes a hypothesis of the form [t=u] into [u=t]

      - [unfold]:
        replace a defined constant by its right-hand side in the goal

      - [unfold... in H]:
        ... or a hypothesis

      - [destruct... as...]:
        case analysis on values of inductively defined types

      - [induction... as...]:
        induction on values of inductively defined types

      - [inversion]:
        reason by injectivity and distinctness of constructors

      - [remember (e) as x]:
        give a name ([x]) to an expression ([e]) so that we can
        destruct [x] without "losing" [e]

      - [assert (e) as H]:
        introduce a "local lemma" [e] and call it [H]
*)

(* ###################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 2 stars, optional (fold_length) *)
(** Many common functions on lists can be implemented in terms of
   [fold].  For example, here is an alternate definition of [length]: *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4,7,0] = 3.
Proof. reflexivity. Qed.

(** Prove the correctness of [fold_length]. *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l. induction l as [| x l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    unfold fold_length.
    unfold fold_length in IHl'.
    simpl.
    apply eq_remove_S. apply IHl'.  Qed.
(** [] *)

(** **** Exercise: 3 stars, recommended (fold_map) *)
(** We can also define [map] in terms of [fold].  Finish [fold_map]
    below. *)

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x s => f x :: s) l [].

(** Write down a theorem in Coq stating that [fold_map] is correct,
    and prove it. *)

Theorem fold_map_correct: forall (X Y : Type) (f : X -> Y) (l : list X),
  fold_map f l = map f l.
Proof.
  intros X Y f l. induction l as [| x l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    unfold fold_map. simpl.
    unfold fold_map in IHl'. simpl in IHl'.
    rewrite -> IHl'. reflexivity.  Qed.
(** [] *)

Module MumbleBaz.
(** **** Exercise: 2 stars, optional (mumble_grumble) *)
(** Consider the following two inductively defined types. *)

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.
Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(** Which of the following are well-typed elements of [grumble X] for
    some type [X]?
      - [d (b a 5)]
      + [d mumble (b a 5)]
      + [d bool (b a 5)]
      + [e bool true]
      + [e mumble (b c 0)]
      - [e bool (b c 0)]
      + [c]
[] *)

(** **** Exercise: 2 stars, optional (baz_num_elts) *)
(** Consider the following inductive definition: *)

Inductive baz : Type :=
   | x : baz -> baz
   | y : baz -> bool -> baz.

(** How _many_ elements does the type [baz] have?
0
[] *)

End MumbleBaz.

(** **** Exercise: 4 stars, recommended (forall_exists_challenge) *)
(** Challenge problem: Define two recursive [Fixpoints],
    [forallb] and [existsb].  The first checks whether every
    element in a list satisfies a given predicate:
      forallb oddb [1,3,5,7,9] = true

      forallb negb [false,false] = true

      forallb evenb [0,2,4,5] = false

      forallb (beq_nat 5) [] = true *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | []      => true
  | x :: l' => if test x then forallb test l' else false
  end.

Example test_forallb_1: forallb oddb [1,3,5,7,9] = true.
Proof. reflexivity.  Qed.

Example test_forallb_2: forallb negb [false,false] = true.
Proof. reflexivity.  Qed.

Example test_forallb_3: forallb evenb [0,2,4,5] = false.
Proof. reflexivity.  Qed.

Example test_forallb_4: forallb (beq_nat 5) [] = true.
Proof. reflexivity.  Qed.

(** The function [existsb] checks whether there exists an element in
    the list that satisfies a given predicate:
      existsb (beq_nat 5) [0,2,3,6] = false

      existsb (andb true) [true,true,false] = true

      existsb oddb [1,0,0,0,0,3] = true

      existsb evenb [] = false *)

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | []      => false
  | x :: l' => if test x then true else existsb test l'
  end.

Example test_existb_1: existsb (beq_nat 5) [0,2,3,6] = false.
Proof. reflexivity.  Qed.

Example test_existb_2: existsb (andb true) [true,true,false] = true.
Proof. reflexivity.  Qed.

Example test_existb_3: existsb oddb [1,0,0,0,0,3] = true.
Proof. reflexivity.  Qed.

Example test_existb_4: existsb evenb [] = false.
Proof. reflexivity.  Qed.

(** Next, create a _nonrecursive_ [Definition], [existsb'], using
    [forallb] and [negb]. *)

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb (fun x => negb (test x)) l).

(** Prove that [existsb'] and [existsb] have the same behavior. *)

Theorem existsb_correct: forall X (f : X -> bool) (l : list X),
  existsb f l = existsb' f l.
Proof.
  intros X f l. unfold existsb'. induction l as [| x l'].
  Case "l = []".
    reflexivity.
  Case "l = x :: l'".
    simpl. destruct (f x).
    SCase "f x = true". reflexivity.
    SCase "f x = false". rewrite -> IHl'. reflexivity.  Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (index_informal) *)
(** Recall the definition of the [index] function:
   Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
     match l with
     | [] => None
     | a :: l' => if beq_nat n O then Some a else index (pred n) l'
     end.
   Write an informal proof of the following theorem:
   forall X n l, length l = n -> @index X (S n) l = None.
(* FILL IN HERE *)
*)
(** [] *)
