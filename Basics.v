(** * Basics: Functional Programming *)

(* $Date: 2012-07-21 13:38:33 -0400 (Sat, 21 Jul 2012) $ *)

(* ###################################################################### *)
(** * Enumerated Types *)

(** In Coq's programming language, almost nothing is built
    in -- not even booleans or numbers!  Instead, it provides powerful
    tools for defining new types of data and functions that process
    and transform them. *)

(* ###################################################################### *)
(** ** Days of the Week *)

(** Let's start with a very simple example.  The following
    declaration tells Coq that we are defining a new set of data
    values -- a "type."  The type is called [day], and its members are
    [monday], [tuesday], etc.  The lines of the definition can be read
    "[monday] is a [day], [tuesday] is a [day], etc." *)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

(** Having defined [day], we can write functions that operate on
    days. *)

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

(** One thing to note is that the argument and return types of
    this function are explicitly declared.  Like most functional
    programming languages, Coq can often work out these types even if
    they are not given explicitly -- i.e., it performs some _type
    inference_ -- but we'll always include them to make reading
    easier. *)

(** Having defined a function, we should check that it works on
    some examples.  There are actually three different ways to do this
    in Coq.  First, we can use the command [Eval simpl] to evaluate a
    compound expression involving [next_weekday].  *)

Eval simpl in (next_weekday friday).
   (* ==> monday : day *)
Eval simpl in (next_weekday (next_weekday saturday)).
   (* ==> tuesday : day *)

(** If you have a computer handy, now would be an excellent
    moment to fire up the Coq interpreter under your favorite IDE --
    either CoqIde or Proof General -- and try this for yourself.  Load
    this file ([Basics.v]) from the book's accompanying Coq sources,
    find the above example, submit it to Coq, and observe the
    result. *)

(** The keyword [simpl] ("simplify") tells Coq precisely how to
    evaluate the expression we give it.  For the moment, [simpl] is
    the only one we'll need; later on we'll see some alternatives that
    are sometimes useful. *)

(** Second, we can record what we _expect_ the result to be in
    the form of a Coq example: *)

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

(** This declaration does two things: it makes an
    assertion (that the second weekday after [saturday] is [tuesday]),
    and it gives the assertion a name that can be used to refer to it
    later. *)
(** Having made the assertion, we can also ask Coq to verify it,
    like this: *)

Proof. simpl. reflexivity.  Qed.

(** The details are not important for now (we'll come back to
    them in a bit), but essentially this can be read as "The assertion
    we've just made can be proved by observing that both sides of the
    equality are the same after simplification." *)

(** Third, we can ask Coq to "extract," from a [Definition], a
    program in some other, more conventional, programming
    language (OCaml, Scheme, or Haskell) with a high-performance
    compiler.  This facility is very interesting, since it gives us a
    way to construct _fully certified_ programs in mainstream
    languages.  Indeed, this is one of the main uses for which Coq was
    developed.  We won't have space to dig further into this topic,
    but more information can be found in the Coq'Art book by Bertot
    and Castéran, as well as the Coq reference manual. *)

(* ###################################################################### *)
(** ** Booleans *)

(** In a similar way, we can define the type [bool] of booleans,
    with members [true] and [false]. *)

Inductive bool : Type :=
  | true : bool
  | false : bool.

(** Although we are rolling our own booleans here for the sake
    of building up everything from scratch, Coq does, of course,
    provide a default implementation of the booleans in its standard
    library, together with a multitude of useful functions and
    lemmas.  (Take a look at [Coq.Init.Datatypes] in the Coq library
    documentation if you're interested.)  Whenever possible, we'll
    name our own definitions and theorems so that they exactly
    coincide with the ones in the standard library. *)

(** Functions over booleans can be defined in the same way as
    above: *)

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(** The last two illustrate the syntax for multi-argument
    function definitions. *)

(** The following four "unit tests" constitute a complete
    specification -- a truth table -- for the [orb] function: *)

Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.

(** _A note on notation_: We use square brackets to delimit
    fragments of Coq code in comments in .v files; this convention,
    also used by the [coqdoc] documentation tool, keeps them visually
    separate from the surrounding text.  In the html version of the
    files, these pieces of text appear in a [different font]. *)

(** The following bit of Coq hackery defines a magic value
    called [admit] that can fill a hole in an incomplete definition or
    proof.  We'll use it in the definition of [nandb] in the following
    exercise.  In general, your job in the exercises is to replace
    [admit] or [Admitted] with real definitions or proofs. *)

Definition admit {T: Type} : T.  Admitted.

(** **** Exercise: 1 star (nandb) *)
(** Complete the definition of the following function, then make
    sure that the [Example] assertions below each can be verified by
    Coq.  *)

(** This function should return [true] if either or both of
    its inputs are [false]. *)

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => negb b2
    | false => true
  end.

(** Remove "[Admitted.]" and fill in each proof with
    "[Proof. simpl. reflexivity. Qed.]" *)

Example test_nandb1:               (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2:               (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3:               (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4:               (nandb true true) = false.
Proof. simpl. reflexivity. Qed.
(** [] *)

(** **** Exercise: 1 star (andb3) *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  andb (andb b1 b2) b3.

Example test_andb31:                 (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32:                 (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33:                 (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34:                 (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.
(** [] *)

(* ###################################################################### *)
(** ** Function Types *)

(** The [Check] command causes Coq to print the type of an
    expression.  For example, the type of [negb true] is [bool]. *)

Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)

(** Functions like [negb] itself are also data values, just like
    [true] and [false].  Their types are called _function types_, and
    they are written with arrows. *)

Check negb.
(* ===> negb : bool -> bool *)

(** The type of [negb], written [bool -> bool] and pronounced
    "[bool] arrow [bool]," can be read, "Given an input of type
    [bool], this function produces an output of type [bool]."
    Similarly, the type of [andb], written [bool -> bool -> bool], can
    be read, "Given two inputs, both of type [bool], this function
    produces an output of type [bool]." *)

(* ###################################################################### *)
(** ** Numbers *)

(** _Technical digression_: Coq provides a fairly fancy module system,
    to aid in organizing large developments.  In this course, we won't
    need most of its features, but one of them is useful: if we
    enclose a collection of declarations between [Module X] and [End
    X] markers, then, in the remainder of the file after the [End],
    all these definitions will be referred to by names like [X.foo]
    instead of just [foo].  This means that the new definition will
    not clash with the unqualified name [foo] later, which would
    otherwise be an error (a name can only be defined once in a given
    scope).  Here, we use this feature to introduce the definition of
    the type [nat] in an inner module so that it does not shadow the
    one from the standard library. *)

Module Playground1.

(** The types we have defined so far are examples of "enumerated
    types": their definitions explicitly enumerate a finite set of
    elements.  A more interesting way of defining a type is to give a
    collection of "inductive rules" describing its elements.  For
    example, we can define the natural numbers as follows: *)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(** The clauses of this definition can be read:
      - [O] is a natural number (note that this is the letter "[O]," not
	the numeral "[0]").
      - [S] is a "constructor" that takes a natural number and yields
	another one -- that is, if [n] is a natural number, then [S n]
	is too.

    Let's look at this in a little more detail.

    Every inductively defined set ([weekday], [nat], [bool], etc.) is
    actually a set of _expressions_.  The definition of [nat] says how
    expressions in the set [nat] can be constructed:

    - the expression [O] belongs to the set [nat];
    - if [n] is an expression belonging to the set [nat], then [S n]
      is also an expression belonging to the set [nat]; and
    - expressions formed in these two ways are the only ones belonging
      to the set [nat]. *)

(** These three conditions are the precise force of the
    [Inductive] declaration.  They imply that the expression [O], the
    expression [S O], the expression [S (S O)], the expression
    [S (S (S O))], and so on all belong to the set [nat], while other
    expressions like [true], [andb true false], and [S (S false)] do
    not.

    We can write simple functions that pattern match on natural
    numbers just as we did above -- for example, predecessor: *)

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

(** The second branch can be read: "if [n] has the form [S n']
    for some [n'], then return [n']."  *)

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

(** Because natural numbers are such a pervasive form of data,
    Coq provides a tiny bit of built-in magic for parsing and printing
    them: ordinary arabic numerals can be used as an alternative to
    the "unary" notation defined by the constructors [S] and [O].  Coq
    prints numbers in arabic form by default: *)

Check (S (S (S (S O)))).
Eval simpl in (minustwo 4).

(** The constructor [S] has the type [nat -> nat], just like the
    functions [minustwo] and [pred]: *)

Check S.
Check pred.
Check minustwo.

(** These are all things that can be applied to a number to yield a
    number.  However, there is a fundamental difference: functions
    like [pred] and [minustwo] come with _computation rules_
    -- e.g., the definition of [pred] says that [pred n] can be
    simplified to [match n with | O => O | S m' => m' end] -- while
    the definition of [S] has no such behavior attached.  Although it
    is a function in the sense that it can be applied to an argument,
    it does not _do_ anything at all! *)

(** For most function definitions over numbers, pure pattern
    matching is not enough: we also need recursion.  For example, to
    check that a number [n] is even, we may need to recursively check
    whether [n-2] is even.  To write such functions, we use the
    keyword [Fixpoint]. *)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

(** When Coq checks this definition, it notes that [evenb] is
    "decreasing on 1st argument."  What this means is that we are
    performing a _structural recursion_ over the argument [n] -- i.e.,
    that we make recursive calls only on strictly smaller values of
    [n].  This implies that all calls to [evenb] will eventually
    terminate.  Coq demands that some argument of _every_ [Fixpoint]
    definition is decreasing. *)

(** We can define [oddb] by a similar [Fixpoint] declaration, but here
    is a simpler definition that will be a bit easier to work with: *)

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Example test_oddb1:    (oddb (S O)) = true.
Proof. simpl. reflexivity.  Qed.
Example test_oddb2:    (oddb (S (S (S (S O))))) = false.
Proof. simpl. reflexivity.  Qed.

(** Naturally, we can also define multi-argument functions by
    recursion.  (Once again, we use a module to avoid polluting the
    namespace.) *)

Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(** Adding three to two now gives us five, as we'd expect. *)

Eval simpl in (plus (S (S (S O))) (S (S O))).

(** The simplification that Coq performs to reach this conclusion can
    be visualized as follows: *)

(*  [plus (S (S (S O))) (S (S O))]
==> [S (plus (S (S O)) (S (S O)))] by the second clause of the [match]
==> [S (S (plus (S O) (S (S O))))] by the second clause of the [match]
==> [S (S (S (plus O (S (S O)))))] by the second clause of the [match]
==> [S (S (S (S (S O))))]          by the first clause of the [match]
*)

(** As a notational convenience, if two or more arguments have
    the same type, they can be written together.  In the following
    definition, [(n m : nat)] means just the same as if we had written
    [(n : nat) (m : nat)]. *)

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

(** You can match two expressions at once by putting a comma
    between them: *)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

(** The _ in the first line is a _wildcard pattern_.  Writing _ in a
    pattern is the same as writing some variable that doesn't get used
    on the right-hand side.  This avoids the need to invent a bogus
    variable name. *)

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Example test_mult1:             (mult 3 3) = 9.
Proof. simpl. reflexivity.  Qed.

(** **** Exercise: 1 star (factorial) *)
(** Recall the standard factorial function:
<<
    factorial(0)  =  1
    factorial(n)  =  n * factorial(n-1)     (if n>0)
>>
    Translate this into Coq. *)

Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => 1
    | S n' => mult n (factorial n')
  end.

Example test_factorial1:          (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2:          (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.
(** [] *)

(** We can make numerical expressions a little easier to read and
    write by introducing "notations" for addition, multiplication, and
    subtraction. *)

Notation "x + y" := (plus x y)
		       (at level 50, left associativity)
		       : nat_scope.
Notation "x - y" := (minus x y)
		       (at level 50, left associativity)
		       : nat_scope.
Notation "x * y" := (mult x y)
		       (at level 40, left associativity)
		       : nat_scope.

Check ((0 + 1) + 1).

(** Note that these do not change the definitions we've already
    made: they are simply instructions to the Coq parser to accept [x
    + y] in place of [plus x y] and, conversely, to the Coq
    pretty-printer to display [plus x y] as [x + y].

    Each notation-symbol in Coq is active in a _notation scope_.  Coq
    tries to guess what scope you mean, so when you write [S(O*O)] it
    guesses [nat_scope], but when you write the cartesian
    product (tuple) type [bool*bool] it guesses [type_scope].
    Occasionally you have to help it out with percent-notation by
    writing [(x*y)%nat], and sometimes in Coq's feedback to you it
    will use [%nat] to indicate what scope a notation is in.

    Notation scopes also apply to numeral notation (3,4,5, etc.), so you
    may sometimes see [0%nat] which means [O], or [0%Z] which means the
    Integer zero. *)

(** When we say that Coq comes with nothing built-in, we really
    mean it: even equality testing for numbers is a user-defined
    operation! *)
(** The [beq_nat] function tests [nat]ural numbers for [eq]uality,
    yielding a [b]oolean.  Note the use of nested [match]es (we could
    also have used a simultaneous match, as we did in [minus].)  *)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
	 | O => true
	 | S m' => false
	 end
  | S n' => match m with
	    | O => false
	    | S m' => beq_nat n' m'
	    end
  end.

(** Similarly, the [ble_nat] function tests [nat]ural numbers for
    [l]ess-or-[e]qual, yielding a [b]oolean. *)

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Example test_ble_nat1:             (ble_nat 2 2) = true.
Proof. simpl. reflexivity.  Qed.
Example test_ble_nat2:             (ble_nat 2 4) = true.
Proof. simpl. reflexivity.  Qed.
Example test_ble_nat3:             (ble_nat 4 2) = false.
Proof. simpl. reflexivity.  Qed.

(** **** Exercise: 2 stars (blt_nat) *)
(** The [blt_nat] function tests [nat]ural numbers for [l]ess-[t]han,
    yielding a [b]oolean.  Instead of making up a new [Fixpoint] for
    this one, define it in terms of a previously defined function.

    Note: If you have trouble with the [simpl] tactic, try using
    [compute], which is like [simpl] on steroids.  However, there is a
    simple, elegant solution for which [simpl] suffices. *)

Definition blt_nat (n m : nat) : bool :=
  (andb (negb (beq_nat n m)) (ble_nat n m)).
 
Example test_blt_nat1:             (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2:             (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3:             (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.
(** [] *)

(* ###################################################################### *)
(** * Proof By Simplification *)

(** Now that we've defined a few datatypes and functions, let's
    turn to the question of how to state and prove properties of their
    behavior.  Actually, in a sense, we've already started doing this:
    each [Example] in the previous sections makes a precise claim
    about the behavior of some function on some particular inputs.
    The proofs of these claims were always the same: use the
    function's definition to simplify the expressions on both sides of
    the [=] and notice that they become identical.

    The same sort of "proof by simplification" can be used to prove
    more interesting properties as well.  For example, the fact that
    [0] is a "neutral element" for [+] on the left can be proved
    just by observing that [0 + n] reduces to [n] no matter what
    [n] is, since the definition of [+] is recursive in its first
    argument. *)

Theorem plus_O_n : forall n:nat, 0 + n = n.
Proof.
  simpl. reflexivity.  Qed.

(** The [reflexivity] command implicitly simplifies both sides of the
    equality before testing to see if they are the same, so we can
    shorten the proof a little. *)
(** (It will be useful later to know that [reflexivity] actually
    does somwhat more than [simpl] -- for example, it tries
    "unfolding" defined terms, replacing them with their right-hand
    sides.  The reason for this difference is that, when reflexivity
    succeeds, the whole goal is finished and we don't need to look at
    whatever expanded expressions [reflexivity] has found; by
    contrast, [simpl] is used in situations where we may have to read
    and understand the new goal, so we would not want it blindly
    expanding definitions.) *)

Theorem plus_O_n' : forall n:nat, 0 + n = n.
Proof.
  reflexivity.  Qed.

(** The form of this theorem and proof are almost exactly the
    same as the examples above: the only differences are that we've
    added the quantifier [forall n:nat] and that we've used the
    keyword [Theorem] instead of [Example].  Indeed, the latter
    difference is purely a matter of style; the keywords [Example] and
    [Theorem] (and a few others, including [Lemma], [Fact], and
    [Remark]) mean exactly the same thing to Coq.

    The keywords [simpl] and [reflexivity] are examples of _tactics_.
    A tactic is a command that is used between [Proof] and [Qed] to
    tell Coq how it should check the correctness of some claim we are
    making.  We will see several more tactics in the rest of this
    lecture, and yet more in future lectures. *)

(** **** Exercise: 1 star, optional (simpl_plus) *)
(** What will Coq print in response to this query? *)

(* Eval simpl in (forall n:nat, n + 0 = n). *)
(* ===> forall n : nat, n + 0 = n : Prop *)

(** What about this one? *)

(* Eval simpl in (forall n:nat, 0 + n = n). *)
(* ===> forall n : nat, n = n : Prop *)

(** Explain the difference.  [] *)

(* ###################################################################### *)
(** * The [intros] Tactic *)

(** Aside from unit tests, which apply functions to particular
    arguments, most of the properties we will be interested in proving
    about programs will begin with some quantifiers (e.g., "for all
    numbers [n], ...") and/or hypothesis ("assuming [m=n], ...").  In
    such situations, we will need to be able to reason by _assuming
    the hypothesis_ -- i.e., we start by saying "OK, suppose [n] is
    some arbitrary number," or "OK, suppose [m=n]."

    The [intros] tactic permits us to do this by moving one or more
    quantifiers or hypotheses from the goal to a "context" of current
    assumptions.

    For example, here is a slightly different proof of the same theorem. *)

Theorem plus_O_n'' : forall n:nat, 0 + n = n.
Proof.
  intros n. reflexivity.  Qed.

(** Step through this proof in Coq and notice how the goal and
    context change. *)

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.

(** The [_l] suffix in the names of these theorems is
    pronounced "on the left." *)

(* ###################################################################### *)
(** * Proof by Rewriting *)

(** Here is a slightly more interesting theorem: *)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

(** Instead of making a completely universal claim about all numbers
    [n] and [m], this theorem talks about a more specialized property
    that only holds when [n = m].  The arrow symbol is pronounced
    "implies."

    Since [n] and [m] are arbitrary numbers, we can't just use
    simplification to prove this theorem.  Instead, we prove it by
    observing that, if we are assuming [n = m], then we can replace
    [n] with [m] in the goal statement and obtain an equality with the
    same expression on both sides.  The tactic that tells Coq to
    perform this replacement is called [rewrite]. *)

Proof.
  intros n m.   (* move both quantifiers into the context *)
  intros H.     (* move the hypothesis into the context *)
  rewrite <- H. (* Rewrite the goal using the hypothesis *)
  reflexivity.  Qed.

(** The first line of the proof moves the universally quantified
    variables [n] and [m] into the context.  The second moves the
    hypothesis [n = m] into the context and gives it the name [H].
    The third tells Coq to rewrite the current goal ([n + n = m + m])
    by replacing the left side of the equality hypothesis [H] with the
    right side.

    (The arrow symbol in the [rewrite] has nothing to do with
    implication: it tells Coq to apply the rewrite from left to right.
    To rewrite from right to left, you can use [rewrite <-].  Try
    making this change in the above proof and see what difference it
    makes in Coq's behavior.) *)

(** **** Exercise: 1 star (plus_id_exercise) *)
(** Remove "[Admitted.]" and fill in the proof. *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o H1 H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.   Qed.
(** [] *)

(** The [Admitted] command tells Coq that we want to give up
    trying to prove this theorem and just accept it as a given.  This
    can be useful for developing longer proofs, since we can state
    subsidiary facts that we believe will be useful for making some
    larger argument, use [Admitted] to accept them on faith for the
    moment, and continue thinking about the larger argument until we
    are sure it makes sense; then we can go back and fill in the
    proofs we skipped.  Be careful, though: every time you say [admit]
    or [Admitted] you are leaving a door open for total nonsense to
    enter Coq's nice, rigorous, formally checked world! *)

(** We can also use the [rewrite] tactic with a previously proved
    theorem instead of a hypothesis from the context. *)

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  Qed.

(** **** Exercise: 2 stars, recommended (mult_1_plus) *)
Theorem mult_1_plus : forall n m : nat,
  (1 + n) * m = m + (n * m).
Proof.
  intros n m.
  rewrite -> plus_1_l.
  simpl.
  reflexivity. Qed.
(** [] *)

(* ###################################################################### *)
(** * Case Analysis *)

(** Of course, not everything can be proved by simple
    calculation: In general, unknown, hypothetical values (arbitrary
    numbers, booleans, lists, etc.) can show up in the "head position"
    of functions that we want to reason about, blocking
    simplification.  For example, if we try to prove the following
    fact using the [simpl] tactic as above, we get stuck. *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. simpl.  (* does nothing! *)
Admitted.

(** The reason for this is that the definitions of both
    [beq_nat] and [+] begin by performing a [match] on their first
    argument.  But here, the first argument to [+] is the unknown
    number [n] and the argument to [beq_nat] is the compound
    expression [n + 1]; neither can be simplified.

    What we need is to be able to consider the possible forms of [n]
    separately.  If [n] is [O], then we can calculate the final result
    of [beq_nat (n + 1) 0] and check that it is, indeed, [false].
    And if [n = S n'] for some [n'], then, although we don't know
    exactly what number [n + 1] yields, we can calculate that, at
    least, it will begin with one [S], and this is enough to calculate
    that, again, [beq_nat (n + 1) 0] will yield [false].

    The tactic that tells Coq to consider, separately, the cases where
    [n = O] and where [n = S n'] is called [destruct]. *)

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity.  Qed.

(** The [destruct] generates _two_ subgoals, which we must then
    prove, separately, in order to get Coq to accept the theorem as
    proved.  (No special command is needed for moving from one subgoal
    to the other.  When the first subgoal has been proved, it just
    disappears and we are left with the other "in focus.")  In this
    proof, each of the subgoals is easily proved by a single use of
    [reflexivity].

    The annotation "[as [| n']]" is called an "intro pattern."  It
    tells Coq what variable names to introduce in each subgoal.  In
    general, what goes between the square brackets is a _list_ of
    lists of names, separated by [|].  Here, the first component is
    empty, since the [O] constructor is nullary (it doesn't carry any
    data).  The second component gives a single name, [n'], since [S]
    is a unary constructor.

    The [destruct] tactic can be used with any inductively defined
    datatype.  For example, we use it here to prove that boolean
    negation is involutive -- i.e., that negation is its own
    inverse. *)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
    reflexivity.
    reflexivity.  Qed.

(** Note that the [destruct] here has no [as] clause because
    none of the subcases of the [destruct] need to bind any variables,
    so there is no need to specify any names.  (We could also have
    written "[as [|]]", or "[as []]".)  In fact, we can omit the [as]
    clause from _any_ [destruct] and Coq will fill in variable names
    automatically.  Although this is convenient, it is arguably bad
    style, since Coq often makes confusing choices of names when left
    to its own devices. *)

(** **** Exercise: 1 star (zero_nbeq_plus_1) *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n.
    reflexivity.
    reflexivity.
Qed.
(** [] *)

(* ###################################################################### *)
(** * Naming Cases *)

(** The fact that there is no explicit command for moving from
    one branch of a case analysis to the next can make proof scripts
    rather hard to read.  In larger proofs, with nested case analyses,
    it can even become hard to stay oriented when you're sitting with
    Coq and stepping through the proof.  (Imagine trying to remember
    that the first five subgoals belong to the inner case analysis and
    the remaining seven cases are what remains of the outer one...)
    Disciplined use of indentation and comments can help, but a better
    way is to use the [Case] tactic.

    [Case] is not built into Coq: we need to define it ourselves.
    There is no need to understand how it works -- just skip over the
    definition to the example that follows.  It uses some facilities
    of Coq that we have not discussed -- the string library (just for
    the concrete syntax of quoted strings) and the [Ltac] command,
    which allows us to declare custom tactics.  Kudos to Aaron
    Bohannon for this nice hack! *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

(** Here's an example of how [Case] is used.  Step through the
   following proof and observe how the context changes. *)

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity.  Qed.

(** [Case] does something very trivial: It simply adds a string
    that we choose (tagged with the identifier "Case") to the context
    for the current goal.  When subgoals are generated, this string is
    carried over into their contexts.  When the last of these subgoals
    is finally proved and the next top-level goal (a sibling of the
    current one) becomes active, this string will no longer appear in
    the context and we will be able to see that the case where we
    introduced it is complete.  Also, as a sanity check, if we try to
    execute a new [Case] tactic while the string left by the previous
    one is still in the context, we get a nice clear error message.

    For nested case analyses (i.e., when we want to use a [destruct]
    to solve a goal that has itself been generated by a [destruct]),
    there is an [SCase] ("subcase") tactic. *)

(** **** Exercise: 2 stars (andb_true_elim2) *)
(** Prove [andb_true_elim2], marking cases (and subcases) when
    you use [destruct]. *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  Case "c = true".
    reflexivity.
  Case "c = false".
    rewrite <- H.
    destruct b.
    SCase "b = true".
      reflexivity.
    SCase "b = false".
      reflexivity.     Qed.
(** [] *)

(** There are no hard and fast rules for how proofs should be
    formatted in Coq -- in particular, where lines should be broken
    and how sections of the proof should be indented to indicate their
    nested structure.  However, if the places where multiple subgoals
    are generated are marked with explicit [Case] tactics placed at
    the beginning of lines, then the proof will be readable almost no
    matter what choices are made about other aspects of layout.

    This is a good place to mention one other piece of (possibly
    obvious) advice about line lengths.  Beginning Coq users sometimes
    tend to the extremes, either writing each tactic on its own line
    or entire proofs on one line.  Good style lies somewhere in the
    middle.  In particular, one reasonable convention is to limit
    yourself to 80-character lines.  Lines longer than this are hard
    to read and can be inconvenient to display and print.  Many
    editors have features that help enforce this. *)


(* ###################################################################### *)
(** * Induction *)

(** We proved above that [0] is a neutral element for [+] on
    the left using a simple partial evaluation argument.  The fact
    that it is also a neutral element on the _right_... *)

Theorem plus_0_r_firsttry : forall n:nat,
  n + 0 = n.

(** ... cannot be proved in the same simple way.  Just applying
  [reflexivity] doesn't work: the [n] in [n + 0] is an arbitrary
  unknown number, so the [match] in the definition of [+] can't be
  simplified.  And reasoning by cases using [destruct n] doesn't get
  us much further: the branch of the case analysis where we assume [n
  = 0] goes through, but in the branch where [n = S n'] for some [n']
  we get stuck in exactly the same way.  We could use [destruct n'] to
  get one step further, but since [n] can be arbitrarily large, if we
  try to keep on going this way we'll never be done. *)

Proof.
  intros n.
  simpl. (* Does nothing! *)
Admitted.

(** Case analysis gets us a little further, but not all the way: *)

Theorem plus_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'].
  Case "n = 0".
    reflexivity. (* so far so good... *)
  Case "n = S n'".
    simpl.       (* ...but here we are stuck again *)
Admitted.

(** To prove such facts -- indeed, to prove most interesting
    facts about numbers, lists, and other inductively defined sets --
    we need a more powerful reasoning principle: _induction_.

    Recall (from high school) the principle of induction over natural
    numbers: If [P(n)] is some proposition involving a natural number
    [n] and we want to show that P holds for _all_ numbers [n], we can
    reason like this:
	 - show that [P(O)] holds;
	 - show that, for any [n'], if [P(n')] holds, then so does
	   [P(S n')];
	 - conclude that [P(n)] holds for all [n].

    In Coq, the steps are the same but the order is backwards: we
    begin with the goal of proving [P(n)] for all [n] and break it
    down (by applying the [induction] tactic) into two separate
    subgoals: first showing [P(O)] and then showing [P(n') -> P(S
    n')].  Here's how this works for the theorem we are trying to
    prove at the moment: *)

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".     reflexivity.
  Case "n = S n'".  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Like [destruct], the [induction] tactic takes an [as...]
    clause that specifies the names of the variables to be introduced
    in the subgoals.  In the first branch, [n] is replaced by [0] and
    the goal becomes [0 + 0 = 0], which follows by simplification.  In
    the second, [n] is replaced by [S n'] and the assumption [n' + 0 =
    n'] is added to the context (with the name [IHn'], i.e., the
    Induction Hypothesis for [n']).  The goal in this case becomes [(S
    n') + 0 = S n'], which simplifies to [S (n' + 0) = S n'], which in
    turn follows from the induction hypothesis. *)

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** **** Exercise: 2 stars, recommended (basic_induction) *)
Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n'].
  Case "n = 0".
    rewrite -> plus_0_r. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity. Qed.
(** [] *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** **** Exercise: 2 stars (double_plus) *)
Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity. Qed.
(** [] *)

(** **** Exercise: 1 star (destruct_induction) *)
(** Briefly explain the difference between the tactics
    [destruct] and [induction].

(* FILL IN HERE *)

*)
(** [] *)

(* ###################################################################### *)
(** * Formal vs. Informal Proof *)

(** "Informal proofs are algorithms; formal proofs are code." *)

(** The question of what, exactly, constitutes a "proof" of a
    mathematical claim has challenged philosophers for millenia.  A
    rough and ready definition, though, could be this: a proof of a
    mathematical proposition [P] is a written (or spoken) text that
    instills in the reader or hearer the certainty that [P] is true.
    That is, a proof is an act of communication.

    Now, acts of communication may involve different sorts of readers.
    On one hand, the "reader" can be a program like Coq, in which case
    the "belief" that is instilled is a simple mechanical check that
    [P] can be derived from a certain set of formal logical rules, and
    the proof is a recipe that guides the program in performing this
    check.  Such recipes are _formal_ proofs.

    Alternatively, the reader can be a human being, in which case the
    proof will be written in English or some other natural language,
    thus necessarily _informal_.  Here, the criteria for success are
    less clearly specified.  A "good" proof is one that makes the
    reader believe [P].  But the same proof may be read by many
    different readers, some of whom may be convinced by a particular
    way of phrasing the argument, while others may not be.  One reader
    may be particularly pedantic, inexperienced, or just plain
    thick-headed; the only way to convince them will be to make the
    argument in painstaking detail.  But another reader, more familiar
    in the area, may find all this detail so overwhelming that they
    lose the overall thread.  All they want is to be told the main
    ideas, because it is easier to fill in the details for themselves.
    Ultimately, there is no universal standard, because there is no
    single way of writing an informal proof that is guaranteed to
    convince every conceivable reader.  In practice, however,
    mathematicians have developed a rich set of conventions and idioms
    for writing about complex mathematical objects that, within a
    certain community, make communication fairly reliable.  The
    conventions of this stylized form of communication give a fairly
    clear standard for judging proofs good or bad.

    Because we are using Coq in this course, we will be working
    heavily with formal proofs.  But this doesn't mean we can ignore
    the informal ones!  Formal proofs are useful in many ways, but
    they are _not_ very efficient ways of communicating ideas between
    human beings. *)

(** For example, here is a proof that addition is associative: *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Coq is perfectly happy with this as a proof.  For a human,
    however, it is difficult to make much sense of it.  If you're used
    to Coq you can probably step through the tactics one after the
    other in your mind and imagine the state of the context and goal
    stack at each point, but if the proof were even a little bit more
    complicated this would be next to impossible.  Instead, a
    mathematician mighty write it like this: *)
(** - _Theorem_: For any [n], [m] and [p],
      n + (m + p) = (n + m) + p.
    _Proof_: By induction on [n].

    - First, suppose [n = 0].  We must show
	0 + (m + p) = (0 + m) + p.
      This follows directly from the definition of [+].

    - Next, suppose [n = S n'], where
	n' + (m + p) = (n' + m) + p.
      We must show
	(S n') + (m + p) = ((S n') + m) + p.
      By the definition of [+], this follows from
	S (n' + (m + p)) = S ((n' + m) + p),
      which is immediate from the induction hypothesis. [] *)

(** The overall form of the proof is basically similar.  This is
    no accident, of course: Coq has been designed so that its
    [induction] tactic generates the same sub-goals, in the same
    order, as the bullet points that a mathematician would write.  But
    there are significant differences of detail: the formal proof is
    much more explicit in some ways (e.g., the use of [reflexivity])
    but much less explicit in others; in particular, the "proof state"
    at any given point in the Coq proof is completely implicit,
    whereas the informal proof reminds the reader several times where
    things stand. *)

(** Here is a formal proof that shows the structure more
    clearly: *)

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.   Qed.

(** **** Exercise: 2 stars (plus_comm_informal) *)
(** Translate your solution for [plus_comm] into an informal proof. *)

(** Theorem: Addition is commutative. *)
(** - _Theorem_: For any [n] and [m],
      n + m = m + n.
    _Proof_: By induction on [n].

    - First, suppose [n = 0].  We must show
	0 + m = m + 0.
      This follows from the fact that 0 is a "neutral element" for [+]
      on the right and on the left.

    - Next, suppose [n = S n'], where
	n' + m = m + n'.
      We must show
	(S n') + m = m + (S n').
      By the definition of [+], this follows from
	S (n' + m) = m + (S n'),
      and from induction hypothesis
        S (m + n') = m + (S n'),
      which immediate from the plus_n_Sm. [] *)


(** **** Exercise: 2 stars, optional (beq_nat_refl_informal) *)
(** Write an informal proof of the following theorem, using the
    informal proof of [plus_assoc] as a model.  Don't just
    paraphrase the Coq tactics into English!

    Theorem: [true = beq_nat n n] for any [n].

    Proof: By induction on [n].

    - First, suppose [n = 0]. We must show
        true = beq_nat 0 0.
      This follows directly from the definition of [beq_nat].

    - Next, suppose [n = S n'], where
        true = beq_nat n' n'.
      We must show
        true = beq_nat (S n') (S n').
      By the induction hypothesis, this follows from
        beq_nat n' n' = beq_nat (S n') (S n')
      which is immediate from [beq_nat] definition.
[]
 *)

(** **** Exercise: 1 star, optional (beq_nat_refl) *)
Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    rewrite -> IHn'. reflexivity. Qed.
(** [] *)


(* ###################################################################### *)
(** * Proofs Within Proofs *)

(** In Coq, as in informal mathematics, large proofs are very
    often broken into a sequence of theorems, with later proofs
    referring to earlier theorems.  Occasionally, however, a proof
    will need some miscellaneous fact that is too trivial (and of too
    little general interest) to bother giving it its own top-level
    name.  In such cases, it is convenient to be able to simply state
    and prove the needed "sub-theorem" right at the point where it is
    used.  The [assert] tactic allows us to do this.  For example, our
    earlier proof of the [mult_0_plus] theorem referred to a previous
    theorem named [plus_O_n].  We can also use [assert] to state and
    prove [plus_O_n] in-line: *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
    Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity.  Qed.

(** The [assert] tactic introduces two sub-goals.  The first is
    the assertion itself; by prefixing it with [H:] we name the
    assertion [H].  (Note that we could also name the assertion with
    [as] just as we did above with [destruct] and [induction], i.e.,
    [assert (0 + n = n) as H].  Also note that we mark the proof of
    this assertion with a [Case], both for readability and so that,
    when using Coq interactively, we can see when we're finished
    proving the assertion by observing when the ["Proof of assertion"]
    string disappears from the context.)  The second goal is the same
    as the one at the point where we invoke [assert], except that, in
    the context, we have the assumption [H] that [0 + n = n].  That
    is, [assert] generates one subgoal where we must prove the
    asserted fact and a second subgoal where we can use the asserted
    fact to make progress on whatever we were trying to prove in the
    first place. *)

(** Actually, [assert] will turn out to be handy in many sorts of
    situations.  For example, suppose we want to prove that [(n + m)
    + (p + q) = (m + n) + (p + q)]. The only difference between the
    two sides of the [=] is that the arguments [m] and [n] to the
    first inner [+] are swapped, so it seems we should be able to
    use the commutativity of addition ([plus_comm]) to rewrite one
    into the other.  However, the [rewrite] tactic is a little stupid
    about _where_ it applies the rewrite.  There are three uses of
    [+] here, and it turns out that doing [rewrite -> plus_comm]
    will affect only the _outer_ one. *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)...
     it seems like plus_comm should do the trick! *)
  rewrite -> plus_comm.
  (* Doesn't work...Coq rewrote the wrong plus! *)
Admitted.

(** To get [plus_comm] to apply at the point where we want it, we can
    introduce a local lemma stating that [n + m = m + n] (for
    the particular [m] and [n] that we are talking about here), prove
    this lemma using [plus_comm], and then use this lemma to do the
    desired rewrite. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity.  Qed.

(** **** Exercise: 4 stars, recommended (mult_comm) *)
(** Use [assert] to help prove this theorem.  You shouldn't need to
    use induction. *)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  assert (H2: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H2. reflexivity. Qed.

(** Now prove commutativity of multiplication.  (You will probably
    need to define and prove a separate subsidiary theorem to be used
    in the proof of this one.)  You may find that [plus_swap] comes in
    handy. *)

Theorem mult_n_Sm : forall n m : nat,
 n * S m = n + n * m.
Proof.
  intros n m. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    rewrite -> plus_swap.
    reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  intros m n. induction m as [| m'].
  Case "m = 0".
    rewrite -> mult_0_r.
    reflexivity.
  Case "m = S m'".
    rewrite -> mult_n_Sm.
    rewrite <- IHm'.
    reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (evenb_n__oddb_Sn) *)
Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    assert (H: evenb (S (S n')) = evenb n').
    SCase "Proof of assertion".
      reflexivity.
    rewrite -> H.
    rewrite -> IHn'.
    rewrite -> negb_involutive.
    reflexivity.
Qed.
(** [] *)

(* ###################################################################### *)
(** * More Exercises *)

(** **** Exercise: 3 stars, optional (more_exercises) *)
(** Take a piece of paper.  For each of the following theorems, first
    _think_ about whether (a) it can be proved using only
    simplification and rewriting, (b) it also requires case
    analysis ([destruct]), or (c) it also requires induction.  Write
    down your prediction.  Then fill in the proof.  (There is no need
    to turn in your piece of paper; this is just to encourage you to
    reflect before hacking!) *)

Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    rewrite -> IHn'. reflexivity. Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  reflexivity. Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b. destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    reflexivity. Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p H. induction p as [| p'].
  Case "p = 0".
    simpl. rewrite -> H. reflexivity.
  Case "p = S p'".
    simpl. rewrite -> IHp'. reflexivity. Qed.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  reflexivity. Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n. destruct n as [| n'].
  Case "n = 0".
    rewrite -> mult_0_r. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> plus_0_r. reflexivity. Qed.

Theorem all3_spec : forall b c : bool,
  orb (andb b c)
      (orb (negb b)
           (negb c))
  = true.
Proof.
  intros b c. destruct b.
  Case "b = true".
    destruct c.
    SCase "c = true".
      reflexivity.
    SCase "c = false".
      reflexivity.
  Case "b = false".
    destruct c.
    SCase "c = true".
      reflexivity.
    SCase "c = false".
      reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction p as [| p'].
  Case "p = 0".
    rewrite -> mult_0_r.
    rewrite -> mult_0_r.
    rewrite -> mult_0_r.
    reflexivity.
  Case "p = S p'".
    assert (H1: forall k, k * S p' = S p' * k).
      intros k. rewrite -> mult_comm. reflexivity.
    rewrite -> H1.
    rewrite -> H1.
    rewrite -> H1.
    simpl.
    assert (H2: forall k : nat, p' * k = k * p').
      intros k. rewrite -> mult_comm. reflexivity.
    rewrite -> H2.
    rewrite -> H2.
    rewrite -> H2.
    rewrite -> IHp'.
    rewrite -> plus_assoc.
    rewrite -> plus_assoc.
    assert (H3: n + n * p' + m = m + n + n * p').
      rewrite -> plus_comm. rewrite -> plus_assoc. reflexivity.
    rewrite -> H3.
    assert (H4: n + m = m + n).
      rewrite -> plus_comm. reflexivity.
    rewrite -> H4.
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    rewrite -> mult_plus_distr_r.
    reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (plus_swap') *)
(** The [replace] tactic allows you to specify a particular subterm to
   rewrite and what you want it rewritten to.  More precisely,
   [replace (t) with (u)] replaces (all copies of) expression [t] in
   the goal by expression [u], and generates [t = u] as an additional
   subgoal. This is often useful when a plain [rewrite] acts on the wrong
   part of the goal.

   Use the [replace] tactic to do a proof of [plus_swap'], just like
   [plus_swap] but without needing [assert (n + m = m + n)].
*)

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  replace (n + m) with (m + n).
  reflexivity.
  Case "Proof of replace".
    rewrite -> plus_comm.
    reflexivity.
Qed.
(** [] *)


(** **** Exercise: 3 stars, optional *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b.
  Case "b = true".
  remember (f true) as ftrue.
    destruct ftrue.
    SCase "f true = true".
      rewrite <- Heqftrue.
      symmetry.
      apply Heqftrue.
    SCase "f true = false".
      remember (f false) as ffalse.
      destruct ffalse.
      SSCase "f false = true".
	symmetry.
	apply Heqftrue.
      SSCase "f false = false".
	symmetry.
	apply Heqffalse.
  Case "b = false".
  remember (f false) as ffalse.
    destruct ffalse.
    SCase "f false = true".
      remember (f true) as ftrue.
      destruct ftrue.
      SSCase "f true = true".
	symmetry.
	apply Heqftrue.
      SSCase "f true = false".
	symmetry.
	apply Heqffalse.
    SCase "f false = false".
      rewrite <- Heqffalse.
      symmetry.
      apply Heqffalse.
Qed.
(** [] *)

(** **** Exercise: 4 stars, recommended (binary) *)
(** Consider a different, more efficient representation of natural
    numbers using a binary rather than unary system.  That is, instead
    of saying that each natural number is either zero or the successor
    of a natural number, we can say that each binary number is either

      - zero,
      - twice a binary number, or
      - one more than twice a binary number.

    (a) First, write an inductive definition of the type [bin]
	corresponding to this description of binary numbers.

    (Hint: recall that the definition of [nat] from class,
    Inductive nat : Type :=
      | O : nat
      | S : nat -> nat.
    says nothing about what [O] and [S] "mean".  It just says "[O] is
    a nat (whatever that is), and if [n] is a nat then so is [S n]".
    The interpretation of [O] as zero and [S] as successor/plus one
    comes from the way that we use nat values, by writing functions to
    do things with them, proving things about them, and so on.  Your
    definition of [bin] should be correspondingly simple; it is the
    functions you will write next that will give it mathematical
    meaning.)

    (b) Next, write an increment function for binary numbers, and a
	function to convert binary numbers to unary numbers.

    (c) Finally, prove that your increment and binary-to-unary
	functions commute: that is, incrementing a binary number and
	then converting it to unary yields the same result as first
	converting it to unary and then incrementing.
*)
Inductive bin : Type :=
  | Z : bin
  | T : bin -> bin
  | M : bin -> bin.

Fixpoint inc (b : bin) : bin :=
  match b with
    | Z    => M Z         (* 0      -> 1        *)
    | T b' => M b'        (* 2n     -> 2n + 1   *)
    | M b' => T (inc b')  (* 2n + 1 -> 2(n + 1) *)
  end.

Fixpoint bin2nat (b : bin) : nat :=
  match b with
    | Z    => O
    | T b' => double (bin2nat b')
    | M b' => S (double (bin2nat b'))
  end.

Example test_inc: bin2nat (inc (T (M (M Z)))) = 7.
Proof. reflexivity. Qed.

Theorem inc_bin2nat_comm: forall b,
  bin2nat (inc b) = S (bin2nat b).
Proof.
  intros b. induction b as [| b'| b'].
  Case "b = Z".
    reflexivity.
  Case "b = T b'".
    reflexivity.
  Case "b = M b'".
    simpl. rewrite -> IHb'. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 5 stars (binary_inverse) *)
(** This exercise is a continuation of the previous exercise about
    binary numbers.  You will need your definitions and theorems from
    the previous exercise to complete this one.

    (a) First, write a function to convert natural numbers to binary
	numbers.  Then prove that starting with any natural number,
	converting to binary, then converting back yields the same
	natural number you started with.
*)

Fixpoint nat2bin (n : nat) : bin :=
  match n with
    | O    => Z
    | S n' => inc (nat2bin n')
  end.

Theorem nat2bin_inverse: forall (n : nat),
  bin2nat (nat2bin n) = n.
Proof.
  intros. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> inc_bin2nat_comm.
    rewrite -> IHn'.
    reflexivity.
Qed.

(**
    (b) You might naturally think that we should also prove the
	opposite direction: that starting with a binary number,
	converting to a natural, and then back to binary yields the
	same number we started with.  However, it is not true!
	Explain what the problem is.

    (c) Define a function [normalize] from binary numbers to binary
	numbers such that for any binary number b, converting to a
	natural and then back to binary yields [(normalize b)].  Prove
	it.
*)
Definition twice (b : bin) : bin :=
  match b with
    | Z => Z
    | c => T c
  end.

Fixpoint normalize (b : bin) : bin :=
  match b with
    | Z => Z
    | T b' => twice (normalize b')
    | M b' => inc (twice (normalize b'))
  end.

Theorem inc_twice: forall b,
  inc (inc (twice b)) = twice (inc b).
Proof.
  intros b. destruct b as [|b' |b' ].
  SCase "b = Z".    reflexivity.
  SCase "b = T b'". reflexivity.
  SCase "b = M b'". reflexivity.
Qed.

Theorem double_nat2bin_comm: forall n,
  nat2bin (double n) = twice (nat2bin n).
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite -> inc_twice. reflexivity. Qed.

Theorem bin2nat_inverse : forall b,
  nat2bin (bin2nat b) = normalize b.
Proof.
  intros b. induction b as [| b' | b'].
  Case "b = Z".
    reflexivity.
  Case "b = T b'".
    simpl.
    rewrite -> double_nat2bin_comm.
    rewrite -> IHb'.
    reflexivity.
  Case "b = M b'".
    simpl.
    rewrite -> double_nat2bin_comm.
    rewrite -> IHb'.
    reflexivity.
Qed.

(** **** Exercise: 2 stars, optional (decreasing) *)
(** The requirement that some argument to each function be
    "decreasing" is a fundamental feature of Coq's design: In
    particular, it guarantees that every function that can be defined
    in Coq will terminate on all inputs.  However, because Coq's
    "decreasing analysis" is not very sophisticated, it is sometimes
    necessary to write functions in slightly unnatural ways.

    To get a concrete sense of this, find a way to write a sensible
    [Fixpoint] definition (of a simple function on numbers, say) that
    _does_ terminate on all inputs, but that Coq will _not_ accept
    because of this restriction.

Fixpoint f (n : nat) : nat := f (pred n)
  match n with
    | O => O
    | m => f (pred m)
  end.

[] *)
