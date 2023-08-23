(* This file contains five theorems. In each
case, replace the "Admitted" keyword with a
proof and make sure you pass Qed. You can prove
your own lemmas and use them in your solution.
You can also copy the theorems proven in class
and use them as lemmas. Make sure you rename
them to lemmas, if you do so. However, you are
not allowed to use any other lemmas. Make sure
you remove the word "Admitted" from this file
before you submit. *)



Lemma lm0:
  forall m : nat, m*0 = 0.
Proof.
induction m;simpl.
reflexivity.
rewrite IHm.
reflexivity.
Qed.


Lemma helper : forall a b : nat, S ( a + b) = a + S b.
Proof.
  intros.
  induction a; simpl.
  reflexivity.
  rewrite IHa.
  reflexivity.
Qed.

Lemma lm1:
  forall n m p : nat,
    n + (m + p) = m + (n+p).
Proof.
intros.
induction n; simpl.
reflexivity.
rewrite IHn.
rewrite helper.
reflexivity.
Qed.


Lemma lm2:
  forall m n: nat,
    n + n * m = n * S m.
Proof.
intros.
induction n; simpl.
reflexivity.
rewrite <- IHn.
rewrite lm1.
reflexivity.
Qed.



Lemma lm22:
  forall n : nat, n + 0 = n.
Proof.
intros.
induction n; simpl.
reflexivity.
rewrite IHn.
reflexivity.
Qed.



Lemma lm3:
  forall m n : nat, m * n = n * m.
Proof.
intros.
induction n; simpl.
rewrite lm0.
reflexivity.
rewrite <- lm2.
rewrite IHn.
reflexivity.
Qed.



Lemma lm4:
  forall a b : nat, a + b = b + a.
Proof.
intros.
induction a .
simpl.
rewrite lm22.
reflexivity.
simpl.
rewrite IHa.
rewrite helper.
reflexivity.
Qed.


Lemma lm5:
  forall m n k : nat, m + n + k = m + (n + k).
Proof.
intros.
induction m; induction n; induction k; simpl.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
rewrite lm22.
reflexivity.
rewrite lm22.
reflexivity.
rewrite lm22.
rewrite lm22.
reflexivity.
rewrite IHm.
simpl.
reflexivity.
Qed.

Lemma lm6 :
  forall a b c: nat, a * (b + c) = a * b + a * c.
Proof.
intros.
induction a.
simpl.
reflexivity.
simpl.
rewrite IHa.
rewrite <- lm5.
rewrite <- lm5.
assert (G:= lm4 (b+ a * b) c).
rewrite G.
rewrite <- lm5.
assert (G2:= lm4 b c).
rewrite G2.
reflexivity.
Qed.


Lemma lm7 : 
  forall a b c: nat, a * b * c = a * (b * c).
Proof.
intros.
induction a.
simpl.
reflexivity.
simpl.
rewrite lm3.
rewrite <- IHa.
rewrite lm6.
rewrite lm3.
rewrite (lm3 (c) (a*b)).
reflexivity.
Qed.

Lemma lm9 :
  forall a: nat, S a = a + 1.
Proof.
intro.
induction a; simpl.
reflexivity.
rewrite IHa.
reflexivity.
Qed.

Lemma lm10 :
  forall a: nat, a+a=2*a.
Proof.
intros.
induction a; simpl.
reflexivity.
rewrite lm4.
rewrite helper.
rewrite lm22.
rewrite (lm4 a (S a)).
rewrite helper.
reflexivity.
Qed.


Theorem th1 : 
  forall a b c: nat, a * b * c = b * c * a.
Proof.
  intros.
  rewrite (lm3 a b).
  rewrite lm7.
  rewrite (lm3 a c).
  rewrite <- lm7.
  reflexivity.
Qed.
  
  
(* This function computes the sum of all 
integers from 1 to n *)
Fixpoint sum (n : nat) : nat :=
  match n with 
  | O => O
  | S m => sum (m) + n
  end.

Theorem th2 :
  forall n : nat, 2 * sum n = n * (n+1).
Proof.
  intro.
  induction n ; simpl.
  reflexivity.
  rewrite <- lm5.
  rewrite <- lm5.
  rewrite helper.
  rewrite helper.
  rewrite lm6.
  rewrite helper.
  rewrite <- lm5.
  rewrite (lm5 (sum n) (S n) (sum n)).
  rewrite (lm4 (S n) (sum n)).
  rewrite <- (lm5 (sum n) (sum n) (S n)).
  rewrite lm10.
  rewrite IHn.
  rewrite (lm9 n).
  rewrite (lm9 (n*2)).
  rewrite <- lm5.
  rewrite lm6.
  rewrite lm22.
  rewrite <- lm5.
  rewrite <- lm5.
  rewrite (lm3 n 2).
  rewrite <- (lm10 n).
  rewrite <- lm5.
  rewrite (lm3 n 1).
  simpl.
  rewrite lm22.
  rewrite (lm5 (n * n + n + n) 1 n).
  rewrite (lm4 1 n).
  rewrite <- lm5.
  rewrite (lm4 (n+1) (n*n)).
  rewrite <- lm5.
  rewrite (lm5 (n * n + n) 1 _).
  rewrite (lm5 (n * n + n) (1+n) _).
  rewrite (lm5 1 n n).
  rewrite (lm4 1 (n+n)).
  rewrite <- lm5.
  rewrite <- lm5.
  reflexivity.
Qed.


  
Theorem th3: 
  forall a b c : nat,
      and ((a * b) * c = a * (b * c))
          (a*(b + c) = a*b + a*c).
Proof.
  intros.
  split.
  apply lm7.
  apply lm6.
Qed.


(* The following type defines binary natural
numbers that are written in a reversed format.
Here, we use o for 0 and i for 1. If b
is a binary number, O b is the same number with
a zero at the "end" and 1 b is defined 
similarly *)

Inductive binary : Type :=
  | o
  | i
  | O (b: binary)
  | I (b: binary).

 
(* The following function translates numbers
from binary to nat *)

Fixpoint b_to_nat (b: binary) : nat :=
  match b with
  | o => 0
  | i => 1
  | O b' => 2 * (b_to_nat b')
  | I b' => 2 * (b_to_nat b') + 1
  end.

(* Complete the following function, which 
should perform the opposite translation, 
converting nat to binary *)
Fixpoint binaryAdd (b: binary) : binary :=
  match b with
    |o => i
    |i => O i
    |O b' => I b'
    |I b' => O (binaryAdd(b'))
  end.

Fixpoint nat_to_b (n : nat) : binary :=
  match n with
  |0 => o
  |1 => i
  |S n'=> binaryAdd (nat_to_b n')
  end.



(* Complete the following definition,
  which should return true if the two
  given binary numbers are equal
  and false otherwise. Feel free to
  use a recursive definition if you
  like *)

Fixpoint eq (n m: nat) : bool :=
  match n, m with
  | 0, 0 => true
  | 0, _ => false
  | _, 0 => false
  | S n', S m' => eq n' m'
  end.

Definition binary_eq (b1 b2: binary) : bool :=
  match b1, b2 with
  |_,_ => eq (b_to_nat b1) (b_to_nat b2)
  end.

Compute binary_eq (I(O(I i))) (I(O(I i))).
(* Finally, prove the following theorems *)

Lemma lm16:
  nat_to_b 0 = o.
Proof.
compute.
reflexivity.
Qed.



Lemma lm17:
  forall b: binary, b_to_nat(O b)= 2*b_to_nat(b).
Proof.
intros.
induction b; simpl; reflexivity.
Qed.


Lemma lm19:
  forall n: nat,  nat_to_b(S n) =  binaryAdd(nat_to_b(n)).
Proof.
intros.
induction n.
compute.
reflexivity.
simpl.
reflexivity. (*wtf is this*)
Qed.

Lemma lm21:
  forall n:nat, 2*S n = 2*n + 2.
Proof.
intros.
rewrite lm3. (* S n * n can be simpl. *)
rewrite lm9.
rewrite lm3.
rewrite lm6.
simpl.
rewrite lm22.
reflexivity.
Qed.


Lemma lm18:
  forall n: nat, binary_eq (O(nat_to_b n)) (nat_to_b(2*n)) = true.
Proof.
intros.
induction n.
compute.
reflexivity.
rewrite lm19.
rewrite lm21.
assert (2*n+2=(S (2*n+1))).
rewrite (lm9 (2*n+1)).
rewrite (lm5 (2*n) 1 1).
simpl.
rewrite lm22.
reflexivity.
rewrite H.
rewrite lm19.
Abort.

Lemma asso4:
  forall a b c d: nat, a+b+c+d = a+(b+c)+d.
Proof.
intros.
induction a.
simpl.
reflexivity.
simpl.
rewrite IHa.
reflexivity.
Qed.

Lemma lm20:
  forall b: binary,  b_to_nat(binaryAdd(b)) = b_to_nat(b)+1.
Proof.

intros.
induction b;simpl.
reflexivity.
reflexivity.
reflexivity.
rewrite lm22.
rewrite lm22.
rewrite IHb.
rewrite <- lm5.
rewrite (asso4 (b_to_nat b) (1) (b_to_nat b) (1)).
rewrite (lm4 1 (b_to_nat b)).
rewrite <- asso4.
reflexivity.
Qed.

Theorem th4: 
  forall n : nat, b_to_nat (nat_to_b n) = n.
Proof.
  intros.
  induction n.
  compute.
  reflexivity.
  rewrite lm19.
  rewrite lm20.
  rewrite IHn.
  rewrite <- lm9.
  reflexivity.
Qed.





Theorem th5:
  forall b : binary, binary_eq b (nat_to_b (b_to_nat b)) = true.
Proof.
  intro.
  induction (b).
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  
  rewrite lm17.

  
  rewrite lm17.


(* Have fun proving! *)






