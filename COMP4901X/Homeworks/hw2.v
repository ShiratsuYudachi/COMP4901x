Module Hoare.

From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.


Definition total_map (A : Type) := string -> A.

Definition t_empty {A: Type} (default : A) : total_map A := (fun _ => default).

Definition t_update {A: Type} (m: total_map A)(x: string)(v: A) :=
   fun x' => if eqb x x' then v else m x'.


Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).
Notation "x '!->' v" := (x !-> v ; t_empty 0) (at level 100).



Definition state := total_map nat.

Inductive aexp : Type :=
  | ANum (n : nat)

  | AId (x : string) 

  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* Let's define notation to simplify our WHILE programs *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.

Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y" := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y" := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).
Open Scope com_scope.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Check <{ 3 + (X * 2) }>.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}> => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}> => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}> => negb (beval st b1)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
  end.

(* Let's define statements in our WHILE language *)

(* c := skip | x := a | c ; c | if b then c else c end
         | while b do c end *)

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

(* Let's define notation *)

Notation "'skip'" :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.


Definition fact_in_WHILE : com :=
  <{ Z := X;
     Y := 1;
     while Z <> 0 do
       Y := Y * Z;
       Z := Z - 1
     end }>.

Print fact_in_WHILE.

Definition a_temp := <{ 1 + 2 }>.
Print a_temp.

Definition b_temp := <{(true && ~ (X <= 4))}>.
Print b_temp.

Definition c_temp := <{ X := X + 2 }>.
Print c_temp.

Definition subtract_slowly_body : com :=
  <{ Z := Z - 1 ;
     X := X - 1 }>.

Definition subtract_slowly : com :=
  <{ while X <> 0 do
       subtract_slowly_body
     end }>.

Definition subtract_3_from_5_slowly : com :=
  <{ X := 3 ;
     Z := 5 ;
     subtract_slowly }>.

Definition infinite_loop : com :=
  <{ while true do
       skip
     end }>.

(* Let's define our semantics *)

(* Denotational first *)

Fixpoint ceval_no_while (st : state) (c : com) : state :=
  match c with
    | <{ skip }> =>
        st
    | <{ x := a }> =>
        t_update st x (aeval st a)
    | <{ c1 ; c2 }> =>
        let st' := ceval_no_while st c1 in
        ceval_no_while st' c2
    | <{ if b then c1 else c2 end}> =>
        if (beval st b)
          then ceval_no_while st c1
          else ceval_no_while st c2
    | <{ while b do c end }> =>
        st (* Fixpoint? *)
  end.

Definition initial_state := (Z !-> 4 ; X !-> 2).
Print initial_state.
Definition add_subtract := <{ Z := Z - X ; X := X + 1 }>.
Definition result := ceval_no_while initial_state add_subtract.
Compute result Z.
Compute result X.



(* Let's do operational instead *)

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

(* Can we define small-step Operational semantics? *)

Inductive one_step : state -> com -> state -> com -> Prop :=
  | R_Skip (st: state)(P: com): 
     one_step st <{skip ; P}> st <{P}>
  | R_Assgn (st:state)(x: string)(a: aexp)(n: nat): 
     aeval st a = n ->
     one_step st <{ x := a }> (x !-> n ; st)  <{skip}>
  | R_Seq (st st': state)(P P' Q: com):
     one_step st P st' P' ->
     one_step st <{P; Q}> st' <{ P'; Q }>
  | R_IfTrue (st: state)(b: bexp)(P Q: com):
    beval st b = true ->
    one_step st <{ if b then P else Q end }> st P
  | R_IfFalse (st:state)(b:bexp)(P Q: com):
    beval st b = false ->
    one_step st <{ if b then P else Q end }> st Q
  | R_WhileTrue (st: state)(b: bexp)(P: com):
    beval st b = true ->
    one_step st <{ while b do P end }> st <{ P ; while b do P end }>
  | R_WhileFalse (st:state)(b: bexp)(P: com):
    beval st b = false ->
    one_step st <{ while b do P end }> st <{ skip }>.

Inductive multi_step : state -> com -> state -> com -> Prop :=
  | R_Base (st st': state)(P P': com): 
     one_step st P st' P' -> multi_step st P st' P'
  | R_Tran (st st' st'': state)(P P' P'': com):
      one_step st P st' P' /\ multi_step st' P' st'' P'' ->
      multi_step st P st'' P''.


Notation " << st | c >> ~~> << st' | c' >> " := (multi_step st c st' c')(at level 40).
Notation " << st | c >> ~> << st' | c' >> " := (one_step st c st' c')(at level 40).

Theorem equiv:
  forall (st st': state)(P: com),
    st =[ P ]=> st' <-> << st | P >> ~~> << st' | <{skip}> >>.
Admitted.

Fixpoint repl_aexp(a: aexp)(x: string)(e: aexp) : aexp :=
  match a with
  | ANum n => a
  | AId x' => if eqb x x' then e else x'
  | <{a1 + a2}> => 
      let a1' := repl_aexp a1 x e in
      let a2' := repl_aexp a2 x e in
      <{a1' + a2'}>
  | <{a1 - a2}> =>
      let a1' := repl_aexp a1 x e in
      let a2' := repl_aexp a2 x e in
      <{a1' - a2'}>
  | <{a1 * a2}> =>
      let a1' := repl_aexp a1 x e in
      let a2' := repl_aexp a2 x e in
      <{a1' * a2'}>
  end.

Fixpoint repl(a: bexp)(x: string)(e: aexp) : bexp :=
  match a with
  | <{true}> => <{true}>
  | <{false}> => <{false}>
  | <{a1 = a2}> =>
    let a1' := repl_aexp a1 x e in
    let a2' := repl_aexp a2 x e in
      <{a1' = a2'}>
  | <{a1 <> a2}> =>
    let a1' := repl_aexp a1 x e in
    let a2' := repl_aexp a2 x e in
      <{a1' <> a2'}>
  | <{a1 <= a2}> => 
    let a1' := repl_aexp a1 x e in
    let a2' := repl_aexp a2 x e in
      <{a1' <= a2'}>
  | <{a1 > a2}> =>
    let a1' := repl_aexp a1 x e in
    let a2' := repl_aexp a2 x e in
      <{a1' > a2'}>
  | <{~ b1}> =>
    let b1' := repl b1 x e in
      <{~ b1'}>
  | <{b1 && b2}> => 
    let b1' := repl b1 x e in
    let b2' := repl b2 x e in
      <{b1' && b2'}>
  end.

Definition entails(a b: bexp): Prop :=
  forall st, beval st a = true -> beval st b = true.

Notation " a -.> b " := (entails a b)(at level 40).
    

Inductive hoare: bexp -> com -> bexp -> Prop :=
  | H_Skip (a: bexp):
    hoare a <{skip}> a
  | H_Assgn (a: bexp)(x: string)(e: aexp):
    hoare (repl a x e) <{ x := e }> a
  | H_Seq (a b c: bexp)(P Q: com):
    hoare a P c -> hoare c Q b ->
    hoare a <{ P ; Q }> b
  | H_If (a g b: bexp)(P Q: com):
    hoare <{ a && g }> P b ->
    hoare <{ a && ~(g)}> Q b ->
    hoare a <{if g then P else Q end}> b
  | H_Conseq (a a' b b': bexp)(P: com):
    a' -.> a ->
    b -.> b' ->
    hoare a P b ->
    hoare a' P b'
  | H_while (a b: bexp)(P: com):
    hoare <{a && b}> P a ->
    hoare a <{ while b do P end }> <{~b && a}>.

Notation " [[ a ]] P [[ b ]] " := (hoare a P b)(at level 40).


Lemma lm1 : forall n:nat, n <= 2 \/ n > 2.
Proof.
  intros n.
  destruct (le_lt_dec n 2).
  - left. assumption.
  - right. assumption.
Qed.


Theorem h1: 
  [[ <{true}> ]] <{ X := 12 }> [[ <{X=12}> ]].
Proof.
  apply H_Conseq with (a:=repl <{ X = 12}> X 12)(b:=<{X=12}>).
  simpl.
  compute.
  intros.
  reflexivity.
  unfold entails.
  intros.
  assumption.
  apply H_Assgn.
Qed.

Theorem h2:
  [[ <{ Y > 10 }> ]]
  <{ X := Y }>
  [[ <{X>10 && Y>10}> ]].
Proof.
assert (<{Y>10}> -.> <{Y>10 && Y>10}>).
unfold entails.
intros.
unfold beval.
unfold beval in H.
rewrite H.
reflexivity.

apply H_Conseq with (a:=<{Y>10 && Y>10}>) (b:=<{ X>10 && Y>10}>).
assumption.
unfold entails.
intros.
assumption.
assert(repl <{X>10 && Y>10}> X Y = <{Y>10 && Y>10}>).
reflexivity.
rewrite <- H0.
apply H_Assgn.
Qed.

Lemma lm2: forall n m : nat, n <=? m = true <-> n <= m.
Proof.
  intros n m. split.
  - apply Nat.leb_le.
  - intros H.
    apply Nat.leb_le in H.
    assumption.
Qed.


Lemma multiply_self_eq_true: forall n : nat, (n * n =? n * n) = true.
Proof.
  intro n.
  destruct (n * n =? n * n) eqn:H2.
  reflexivity.
  assert (n * n = n * n) as H by reflexivity.
  apply beq_nat_true_iff in H.
  rewrite H2 in H.
  discriminate.
Qed.

Require Import Lia.

Lemma lm3: forall n m p: nat,
  n>m -> n+p <=? m+p = false.
Proof.
  intros.
  destruct (n + p <=? m + p) eqn:E.
  - apply Nat.leb_le in E. lia.
  - reflexivity.
Qed.


Lemma lm4: forall n:nat,
  negb (n <=? 12) = true -> negb (n<=? 0) = true.
Proof.
  intros.
  destruct n.
  - simpl in H. discriminate H.
  - reflexivity.
Qed.

Theorem h3:
  [[ <{ X > 2 }> ]]
  <{ X := X + 10 }>
  [[ <{X > 0}> ]].
Proof.
  apply H_Conseq with (a:= <{X+10>12}>) (b:=<{X>12}>).
  - 
    unfold entails.
    intros.
    remember (st X) as n.
    assert (n<=2 \/ n>2).
    apply lm1.
    destruct H0.
    apply lm2 in H0.
    unfold beval in H.
    unfold aeval in H.
    rewrite <- Heqn in H.
    rewrite H0 in H.
    discriminate H.
    unfold beval.
    unfold aeval.
    rewrite <- Heqn.
    assert(n+10 <=? 2+10 = false).
    apply lm3.
    assumption.
    simpl in H1.
    rewrite H1.
    reflexivity.

  - unfold entails.
    intros.
    unfold beval.
    unfold beval in H.
    simpl in H.
    simpl.
    apply lm4.
    assumption.

  - assert(repl <{X>12}> X <{X+10}> = <{X+10 >12}>).
    compute.
    reflexivity.
    rewrite <- H.
    apply H_Assgn.
Qed.

Theorem h4:
  [[ <{ Z > 1 && Z <= 4 }> ]] 
  <{ X := Y * Y }>
  [[ <{X*X = X*X}> ]].
Proof.
assert (<{true}> -.> <{X*X = X*X}>).
unfold entails.
intros.
unfold beval.
unfold beval in H.
simpl.
remember (st X) as n.
apply Nat.eqb_eq. (*unfold == bool*)
reflexivity.

assert (<{ Z > 1 && Z <= 4 }> -.> <{true}>).
unfold entails.
intros.
simpl.
reflexivity.

apply H_Conseq with (a:= (<{ Z > 1 && Z <= 4 }>) ) (b:= <{true}>).
unfold entails.
intros.
assumption.
assumption.

apply H_Conseq with (a:= (<{ Z > 1 && Z <= 4 }>) ) (b:= <{ Z > 1 && Z <= 4 }>).
unfold entails.
intros.
assumption.
assumption.

assert (repl <{Z > 1 && Z <= 4}> X <{Y*Y}> = <{Z > 1 && Z <= 4}>).
simpl.
reflexivity.

rewrite <- H1 at 1.
apply H_Assgn.

Qed.

Theorem h5:
  [[ <{ 0 > X * X }> ]]
  <{ X := 1 }>
  [[ <{ X = 100 }> ]].
Proof.
assert (<{ 0 > X * X }> -.> <{false}>).
unfold entails.
intros.
unfold beval.
unfold beval in H.
simpl in H.
assumption.

assert (<{false}> -.> <{1=100}>).
unfold entails.
intros.
simpl.
simpl in H0.
assumption.

apply H_Conseq with (a:=<{false}>)(b:=<{X=100}>).
assumption.
unfold entails.
intros.
assumption.

apply H_Conseq with (a:=<{1=100}>)(b:=<{X=100}>).
assumption.
unfold entails.
intros.
assumption.

assert(repl <{X=100}> X 1 = <{1=100}>).
simpl.
reflexivity.

rewrite <- H1.
apply H_Assgn.

Qed.

Theorem h6:
  [[ <{ false }> ]]
  <{ X := X + 3 }>
  [[ <{ true }> ]].
Proof.
assert (<{X = 0}> -.> <{true}>).
unfold entails.
intros.
unfold beval.
reflexivity.

assert (<{false}> -.> <{X + 3 = 0}>).
unfold entails.
intros.
unfold beval.
simpl.
unfold beval in H0.
remember (st X) as n.
lia.

apply H_Conseq with (a:=<{X + 3 = 0}>) (b:=<{X = 0}>).
unfold entails.
intros.
unfold beval.
simpl.
unfold beval in H1.
remember (st X) as n.
lia.
assumption.

assert(repl <{X=0}> X <{X+3}> = <{X+3=0}>).
simpl.
reflexivity.

rewrite <-H1.
apply H_Assgn.
Qed.


Theorem h7:
  [[ <{ true }> ]]
  <{ while true do skip end }>
  [[ <{ false }> ]].
Proof.

apply H_Conseq with (a:=<{true}>) (b:=<{true && false}>).
unfold entails.
intros.
assumption.
unfold entails.
intros.
simpl.
simpl in H.
assumption.

assert (<{true && false}> -.> <{~true && true}>).
unfold entails.
intros.
compute.
compute in H.
assumption.

apply H_Conseq with (a:=<{true}>)(b:=<{~ true && true}>).
unfold entails.
intros.
assumption.
unfold entails.
intros.
assumption.

apply H_while.

assert (<{true && true}> -.> <{true}>).
unfold entails.
intros.
unfold beval.
lia.

apply H_Conseq with (a:=<{ true }>) (b:=<{true}>).
apply H0.
unfold entails.
intros.
assumption.

apply H_Skip.
Qed.



Theorem h8:
  [[ <{ true }> ]]
  <{ while true do skip end }>
  [[ <{ true }> ]].
Proof.
apply H_Conseq with (a:=<{true}>) (b:=<{false}>).
unfold entails.
intros.
assumption.
unfold entails.
intros.
unfold beval.
lia.

apply h7.
Qed.


Theorem h9:
  [[ <{ false }> ]]
  <{ X := X+3 }>
  [[ <{ true }> ]].
Proof.
assert (<{X = 0}> -.> <{true}>).
unfold entails.
intros.
unfold beval.
reflexivity.

assert (<{false}> -.> <{X + 3 = 0}>).
unfold entails.
intros.
unfold beval.
simpl.
unfold beval in H0.
remember (st X) as n.
lia.

apply H_Conseq with (a:=<{X + 3 = 0}>) (b:=<{X = 0}>).
unfold entails.
intros.
unfold beval.
simpl.
unfold beval in H1.
remember (st X) as n.
lia.
assumption.

assert(repl <{X=0}> X <{X+3}> = <{X+3=0}>).
simpl.
reflexivity.

rewrite <-H1.
apply H_Assgn.
Qed.

Theorem h10:
  [[ <{ X > 0 }> ]]
  <{ X := X+1 ; X:=X+3 }>
  [[ <{ X > 4 }> ]].
Proof.
apply H_Seq with (c:=<{X > 1}>).

assert(<{X>0}> -.> <{X+1>1}>).
unfold entails.
intros.
unfold beval.
simpl.
unfold beval in H.
simpl in H.
remember (st X) as n.
apply negb_true_iff.
apply negb_true_iff in H.
apply Nat.leb_gt.
apply Nat.leb_gt in H.
lia.


apply H_Conseq with (a:=<{X+1>1}>) (b:=<{X>1}>).
  unfold entails.
  intros.
  unfold beval.
  simpl.
  unfold beval in H0.
  simpl in H0.
  apply negb_true_iff.
  apply negb_true_iff in H0.
  apply Nat.leb_gt.
  apply Nat.leb_gt in H0.
  lia.

  unfold entails.
  intros.
  unfold beval.
  simpl.
  unfold beval in H0.
  simpl in H0.
  apply negb_true_iff.
  apply negb_true_iff in H0.
  apply Nat.leb_gt.
  apply Nat.leb_gt in H0.
  lia.

assert (repl <{X > 1}> X <{X+1}> = <{X+1>1}>).
simpl.
reflexivity.
rewrite <-H0.
apply H_Assgn.


assert(<{X>1}> -.> <{X+3>4}>).
unfold entails.
intros.
unfold beval.
simpl.
unfold beval in H.
simpl in H.
remember (st X) as n.
apply negb_true_iff.
apply negb_true_iff in H.
apply Nat.leb_gt.
apply Nat.leb_gt in H.
lia.


apply H_Conseq with (a:=<{X+3>4}>) (b:=<{X>4}>).
  unfold entails.
  intros.
  unfold beval.
  simpl.
  unfold beval in H0.
  simpl in H0.
  apply negb_true_iff.
  apply negb_true_iff in H0.
  apply Nat.leb_gt.
  apply Nat.leb_gt in H0.
  lia.

  unfold entails.
  intros.
  unfold beval.
  simpl.
  unfold beval in H0.
  simpl in H0.
  apply negb_true_iff.
  apply negb_true_iff in H0.
  apply Nat.leb_gt.
  apply Nat.leb_gt in H0.
  lia.

assert (repl <{X > 4}> X <{X+3}> = <{X+3>4}>).
simpl.
reflexivity.

rewrite <-H0.
apply H_Assgn.
Qed.

Theorem h11:
  [[ <{ Y > 1 }> ]]
  <{ if X <= Y then X := Y else X := X + 1 end }>
  [[ <{ X > 0 }> ]].
Proof.
apply H_If.

assert (<{ Y > 1 && X <= Y }> -.> <{Y>0}>).
  unfold entails.
  intros.
  unfold beval.
  simpl.
  unfold beval in H.
  simpl in H.
  apply negb_true_iff.
remember (st Y) as y.
remember (st X) as x.
apply andb_true_iff in H.
  destruct H. 
  apply negb_true_iff in H.
  apply Nat.leb_gt in H.
  apply Nat.leb_gt.
  lia.

apply H_Conseq with (a:=<{ Y > 0 }>)(b:=<{ X > 0 }>).
assumption.
unfold entails.
intros.
assumption.

assert(repl <{X>0}> X Y = <{Y>0}>).
simpl.
reflexivity.
rewrite <- H0.
apply H_Assgn.

assert (<{ Y > 1 && ~ X <= Y }> -.> <{X + 1>0}>).
unfold entails.
intros.
  unfold beval.
  simpl.
  unfold beval in H.
  simpl in H.
  apply andb_true_iff in H.
  destruct H. 
  apply negb_true_iff in H0.
  apply Nat.leb_gt in H0.
  apply negb_true_iff.
  apply Nat.leb_gt.
  lia.

apply H_Conseq with (a:=<{ X + 1 > 0 }>)(b:=<{ X > 0 }>).
assumption.
unfold entails.
intros.
assumption.

assert(repl <{X>0}> X <{X+1}> = <{X+1>0}>).
simpl.
reflexivity.
rewrite <- H0.
apply H_Assgn.
Qed.

Check H_while.

Theorem h12:
  [[ <{ Y > 0 && X = 0 }> ]]
  <{ while 100 > X do X := X + Y end }>
  [[ <{ 100 <= X && X <= 100 + Y }> ]].
Proof.
assert(<{ Y > 0 && X = 0 }> -.> <{X <= 100 + Y}>).
unfold entails.
intros.
unfold beval in H.
unfold beval.
  simpl in H.
  apply andb_true_iff in H.
  destruct H.
  apply Nat.eqb_eq in H0.
  simpl.
  rewrite H0.
  apply Nat.leb_le.
  lia.
  
assert(<{ ~ 100 > X && X <= 100 + Y }> -.> <{ 100 <= X && X <= 100 + Y }>).
unfold entails.
intros.
unfold beval in H0.
unfold beval.
apply andb_true_iff in H0.
destruct H0.
apply andb_true_iff.
split.
apply Nat.leb_le.
apply negb_true_iff in H0.
apply negb_false_iff in H0.
apply Nat.leb_le in H0.
assumption.
assumption.

apply H_Conseq with (a:=<{X <= 100 + Y}>)(b:=<{~ 100 > X && X <= 100 + Y}>).
apply H.
apply H0.

apply H_while.
assert(<{X <= 100 + Y && 100 > X}> -.> <{X + Y <= 100 + Y}>).
unfold entails.
intros.
unfold beval.
unfold beval in H1.
apply andb_true_iff in H1.
destruct H1.
apply negb_true_iff in H2.
apply Nat.leb_gt in H2.
simpl in H2.
simpl.
apply Nat.leb_le.
lia.

apply H_Conseq with (a:=<{X + Y <= 100 + Y}>)(b:=<{X <= 100 + Y}>).
assumption.
unfold entails.
intros.
assumption.

assert(repl <{ X <= 100 + Y }> X <{X+Y}> = <{ X + Y <= 100 + Y }>).
simpl.
reflexivity.
rewrite <- H2.
apply H_Assgn.

Qed.

End Hoare.