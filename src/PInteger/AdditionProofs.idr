module PInteger.AdditionProofs

import PInteger
import Data.Nat

%default total

export
left_PosIdentity : (a : PInteger) -> Pos Z + a = a
left_PosIdentity (Pos 0) = Refl
left_PosIdentity (Pos (S k)) = Refl
left_PosIdentity (Neg 0) = pos0_neg0_equality
left_PosIdentity (Neg (S k)) = Refl

export
left_NegIdentity : (a : PInteger) -> Neg Z + a = a
left_NegIdentity a =  
    rewrite sym pos0_neg0_equality in
      left_PosIdentity a

export
cancelAdd : (a : PInteger) -> a + negate a = 0
cancelAdd (Pos 0) = Refl
cancelAdd (Pos (S k)) = 
  rewrite cancelAdd (assert_smaller (Pos (S k)) $ Pos k) in
  Refl
cancelAdd (Neg 0) = sym pos0_neg0_equality
cancelAdd (Neg (S k)) = 
  rewrite cancelAdd (assert_smaller (Neg (S k)) $ Neg k) in
  Refl

export
combinePos : (a,b : Nat) -> Pos a + Pos b = Pos (a + b)
combinePos a 0 = rewrite plusZeroRightNeutral a in Refl
combinePos 0 b = left_PosIdentity (Pos b)
combinePos (S j) (S k) = Refl

export
combineNeg : (a,b : Nat) -> Neg a + Neg b = Neg (a + b)
combineNeg a 0 = rewrite plusZeroRightNeutral a in Refl
combineNeg 0 b = rewrite sym pos0_neg0_equality in 
                 rewrite left_PosIdentity (Neg b) in 
                          Refl
combineNeg (S a) (S b) = Refl

export
inverse_identity : (a : Nat) -> Pos a + Neg a = Pos Z
inverse_identity 0 = Refl
inverse_identity (S k) = inverse_identity k

export
intPlusCommutative : (a,b : PInteger) -> a + b = b + a
intPlusCommutative (Pos k) (Pos j) = 
  rewrite combinePos k j in
  rewrite combinePos j k in
  rewrite plusCommutative j k in
  Refl
intPlusCommutative (Neg k) (Neg j) = 
  rewrite combineNeg k j in
  rewrite combineNeg j k in
  rewrite plusCommutative j k in
  Refl
intPlusCommutative (Pos k) (Neg j) = posNegCommutative k j
  where 
    posNegCommutative : (n,m : Nat) -> Pos n + Neg m = Neg m + Pos n
    posNegCommutative 0 m = rewrite left_PosIdentity (Neg m) in Refl
    posNegCommutative (S i) 0 = Refl
    posNegCommutative (S n') (S m') = rewrite posNegCommutative n' m' in Refl
intPlusCommutative (Neg k) (Pos j) = negPosCommutative k j
  where 
    negPosCommutative : (n,m : Nat) -> Neg n + Pos m = Pos m + Neg n
    negPosCommutative 0 m = rewrite left_NegIdentity (Pos m) in Refl
    negPosCommutative (S i) 0 = Refl
    negPosCommutative (S n') (S m') = rewrite negPosCommutative n' m' in Refl

exchange_s_pos : (a,b : Nat) -> Pos a + Pos (S b) = Pos (S a) + Pos b
exchange_s_pos a b = 
  rewrite combinePos (S a) b in
  rewrite combinePos a (S b) in
  rewrite plusSuccRightSucc a b in
  Refl

exchange_s_neg : (a,b : Nat) -> Neg a + Neg (S b) = Neg (S a) + Neg b
exchange_s_neg a b = 
  rewrite combineNeg (S a) b in
  rewrite combineNeg a (S b) in
  rewrite plusSuccRightSucc a b in
  Refl

pos_pos_neg_assoc : (n,m,o : Nat) -> (Pos n + Pos m) + Neg o = Pos n + (Pos m + Neg o)
pos_pos_neg_assoc n m 0 = Refl
pos_pos_neg_assoc n 0 (S o') = Refl
pos_pos_neg_assoc 0 (S m') (S o') = rewrite left_PosIdentity (Pos m' + Neg o') in Refl
pos_pos_neg_assoc (S n') (S m') (S o') = 
  rewrite sym $ pos_pos_neg_assoc (S n') m' o' in
  rewrite combinePos (S n') m' in
  rewrite plusSuccRightSucc n' m' in
  Refl

neg_neg_pos_assoc : (n,m,o : Nat) -> (Neg n + Neg m) + Pos o = Neg n + (Neg m + Pos o)
neg_neg_pos_assoc n m 0 = Refl
neg_neg_pos_assoc n 0 (S k) = Refl
neg_neg_pos_assoc 0 (S j) (S k) = rewrite left_NegIdentity (Neg j + Pos k) in Refl
neg_neg_pos_assoc (S i) (S j) (S k) = 
  rewrite sym $ neg_neg_pos_assoc (S i) j k in
  rewrite sym $ plusSuccRightSucc i j in
  rewrite combineNeg (S i) j in
  Refl

neg_pos_pos_assoc : (n,m,o : Nat) -> (Neg n + Pos m) + Pos o = Neg n + (Pos m + Pos o)
neg_pos_pos_assoc n m 0 = Refl
neg_pos_pos_assoc n 0 (S k) = Refl
neg_pos_pos_assoc 0 (S j) (S k) = Refl
neg_pos_pos_assoc (S i) (S j) (S k) = 
  rewrite neg_pos_pos_assoc i j (S k) in
  rewrite combinePos j (S k) in
  Refl

pos_neg_pos_assoc : (n,m,o : Nat) -> (Pos n + Neg m) + Pos o = Pos n + (Neg m + Pos o)
pos_neg_pos_assoc n 0 o = rewrite left_NegIdentity (Pos o) in Refl
pos_neg_pos_assoc 0 (S m') o = rewrite left_PosIdentity (Neg (S m') + Pos o) in Refl
pos_neg_pos_assoc (S n') (S m') 0 = Refl
pos_neg_pos_assoc (S n') (S m') (S o') = 
  rewrite intPlusCommutative (Pos n') (Neg m') in
  rewrite intPlusCommutative (Neg m') (Pos o') in
  rewrite neg_pos_pos_assoc m' n' (S o') in
  rewrite sym $ pos_pos_neg_assoc (S n') o' m' in
  rewrite exchange_s_pos n' o' in
  rewrite intPlusCommutative (Neg m') (Pos (S n') + Pos o') in
  Refl

pos_neg_neg_assoc : (k,j,i : Nat) -> (Pos k + Neg j) + Neg i = Pos k + (Neg j + Neg i)
pos_neg_neg_assoc k j 0 = Refl
pos_neg_neg_assoc k 0 (S i) = Refl
pos_neg_neg_assoc 0 (S j) (S i) = Refl
pos_neg_neg_assoc (S k) (S j) (S i) = 
  rewrite pos_neg_neg_assoc k j (S i) in
  rewrite combineNeg j (S i) in
  Refl

neg_pos_neg_assoc : (k,j,i : Nat) -> (Neg k + Pos j) + Neg i = Neg k + (Pos j + Neg i)
neg_pos_neg_assoc k j 0 = Refl
neg_pos_neg_assoc k 0 (S i) = Refl
neg_pos_neg_assoc 0 (S j) (S i) = rewrite left_NegIdentity (Pos j + Neg i) in Refl
neg_pos_neg_assoc (S k) (S j) (S i) = 
  rewrite intPlusCommutative (Neg k) (Pos j) in
  rewrite intPlusCommutative (Pos j) (Neg i) in
  rewrite pos_neg_neg_assoc j k (S i) in
  rewrite sym $ neg_neg_pos_assoc (S k) i j in
  rewrite sym $ exchange_s_neg k i in
  rewrite intPlusCommutative (Pos j) (Neg k + Neg (S i)) in
  Refl

export
intPlusAssociative : (a, b, c : PInteger) -> (a + b) + c = a + (b + c)
intPlusAssociative (Pos k) (Pos j) (Pos i) = 
  rewrite combinePos k j in
  rewrite combinePos (k+j) i in
  rewrite combinePos j i in
  rewrite combinePos k (j+i) in
  rewrite plusAssociative k j i in
  Refl
intPlusAssociative (Pos k) (Pos j) (Neg i) = pos_pos_neg_assoc k j i
intPlusAssociative (Pos k) (Neg j) (Pos i) = pos_neg_pos_assoc k j i
intPlusAssociative (Pos k) (Neg j) (Neg i) = pos_neg_neg_assoc k j i
intPlusAssociative (Neg k) (Pos j) (Pos i) = neg_pos_pos_assoc k j i
intPlusAssociative (Neg k) (Pos j) (Neg i) = neg_pos_neg_assoc k j i
intPlusAssociative (Neg k) (Neg j) (Pos i) = neg_neg_pos_assoc k j i
intPlusAssociative (Neg k) (Neg j) (Neg i) = 
  rewrite combineNeg k j in
  rewrite combineNeg (k+j) i in
  rewrite combineNeg j i in
  rewrite combineNeg k (j+i) in
  rewrite plusAssociative k j i in
    Refl
