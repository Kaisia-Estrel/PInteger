module PInteger.AdditionProofs

import PInteger
import Data.Nat

%default total

export
combineNegAdd : (a,b : Nat) -> NegS a + NegS b = NegS (S (a + b))
combineNegAdd 0 b = Refl
combineNegAdd (S k) b = Refl

export 
intPlusCommutative : (a,b : PInteger) -> a + b = b + a
intPlusCommutative (Pos a) (Pos b) = rewrite plusCommutative a b in Refl
intPlusCommutative (NegS a) (NegS b) = 
  rewrite combineNegAdd a b in 
  rewrite plusCommutative a b in 
  rewrite sym $ combineNegAdd b a in 
            Refl
intPlusCommutative (Pos a) (NegS b) = posNegCommutative a b
  where 
    posNegCommutative : (n,m : Nat) -> Pos n + NegS m = NegS m + Pos n
    posNegCommutative 0 0 = Refl
    posNegCommutative (S n) 0 = Refl
    posNegCommutative 0 (S m) = Refl
    posNegCommutative (S n) (S m) = 
      rewrite posNegCommutative n m in
      Refl
intPlusCommutative (NegS a) (Pos b) = negPosCommutative a b
  where 
    negPosCommutative : (n,m : Nat) -> NegS n + Pos m = Pos m + NegS n
    negPosCommutative 0 0 = Refl
    negPosCommutative (S k) 0 = Refl
    negPosCommutative 0 (S m) =  Refl
    negPosCommutative (S n) (S m) = 
        rewrite negPosCommutative n m in
          Refl

export
intPlusLeftNeutral : (a : PInteger) -> 0 + a = a
intPlusLeftNeutral (Pos k) = Refl
intPlusLeftNeutral (NegS k) = Refl

export
intPlusRightNeutral : (a : PInteger) -> a + 0 = a
intPlusRightNeutral (Pos k) = rewrite plusZeroRightNeutral k in Refl
intPlusRightNeutral (NegS 0) = Refl
intPlusRightNeutral (NegS (S k)) = Refl

negPosPos_Assoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> NegS a + (Pos b + Pos c) = (NegS a + Pos b) + Pos c
negPosPos_Assoc 0 b c = case b of { 0 => Refl ; S k => Refl }
negPosPos_Assoc (S k) 0 c = Refl
negPosPos_Assoc (S k) (S j) c = negPosPos_Assoc k j c

posPosNeg_Assoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> Pos a + (Pos b + NegS c) = (Pos a + Pos b) + NegS c
posPosNeg_Assoc 0 b c = rewrite intPlusLeftNeutral (Pos b + NegS c) in Refl
posPosNeg_Assoc a 0 c = rewrite plusZeroRightNeutral a in Refl
posPosNeg_Assoc a (S b) 0 = rewrite sym $ plusSuccRightSucc a b in Refl
posPosNeg_Assoc a (S b) (S c) = 
  rewrite posPosNeg_Assoc a b c in 
  rewrite sym $ plusSuccRightSucc a b in 
      Refl

posNegPos_Assoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> Pos a + (NegS b + Pos c) = (Pos a + NegS b) + Pos c
posNegPos_Assoc a b c = 
  rewrite intPlusCommutative (Pos a) (NegS b) in
  rewrite intPlusCommutative (NegS b) (Pos c) in
  rewrite sym $ negPosPos_Assoc b a c in
  rewrite posPosNeg_Assoc a c b in
  rewrite intPlusCommutative (Pos (a + c)) (NegS b) in
  Refl

negNegPos_Assoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> NegS a + (NegS b + Pos c) = (NegS a + NegS b) + Pos c
negNegPos_Assoc a 0 0 =  rewrite (intPlusRightNeutral (NegS a + NegS 0)) in Refl
negNegPos_Assoc a (S b) 0 = rewrite (intPlusRightNeutral (NegS a + NegS (S b))) in Refl
negNegPos_Assoc a 0 (S c) = rewrite combineNegAdd a 0 in rewrite plusZeroRightNeutral a in Refl
negNegPos_Assoc a (S b) (S c) = 
  rewrite negNegPos_Assoc a b c in 
  rewrite combineNegAdd a b in 
  rewrite combineNegAdd a (S b) in 
  rewrite plusSuccRightSucc a b in
          Refl

posNegNeg_Assoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> Pos a + (NegS b + NegS c) = (Pos a + NegS b) + NegS c
posNegNeg_Assoc 0 b c = rewrite intPlusLeftNeutral (NegS b + NegS c) in Refl
posNegNeg_Assoc (S a) 0 c = Refl
posNegNeg_Assoc (S a) (S b) c = 
  rewrite sym $ posNegNeg_Assoc a b c in
  rewrite combineNegAdd b c in
  Refl

negPosNeg_Assoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> NegS a + (Pos b + NegS c) = (NegS a + Pos b) + NegS c
negPosNeg_Assoc a b c =
  rewrite intPlusCommutative (Pos b) (NegS c) in
  rewrite intPlusCommutative (NegS a) (Pos b) in
  rewrite negNegPos_Assoc a c b in 
  rewrite sym $ posNegNeg_Assoc b a c in
  rewrite intPlusCommutative (NegS a + NegS c) (Pos b) in
  Refl

export
intPlusAssociative : (a,b,c : PInteger) -> a + (b + c) = (a + b) + c
intPlusAssociative (Pos a) (Pos b) (Pos c) = rewrite plusAssociative a b c in Refl
intPlusAssociative (NegS a) (Pos b) (Pos c) = negPosPos_Assoc a b c
intPlusAssociative (Pos a) (NegS b) (Pos c) = posNegPos_Assoc a b c
intPlusAssociative (NegS a) (NegS b) (Pos c) = negNegPos_Assoc a b c
intPlusAssociative (Pos a) (Pos b) (NegS c) = posPosNeg_Assoc a b c
intPlusAssociative (NegS a) (Pos b) (NegS c) = negPosNeg_Assoc a b c
intPlusAssociative (Pos a) (NegS b) (NegS c) = posNegNeg_Assoc a b c
intPlusAssociative (NegS a) (NegS b) (NegS c) = 
  rewrite combineNegAdd a b in
  rewrite combineNegAdd b c in
  rewrite combineNegAdd a (S (b + c)) in
  rewrite sym $ plusSuccRightSucc a (b + c) in
  rewrite plusAssociative a b c in
  Refl

export 
intPlusRightIdentity : (a : PInteger) -> a + 0 = a
intPlusRightIdentity (Pos k) = rewrite plusZeroRightNeutral k in Refl
intPlusRightIdentity (NegS 0) = Refl
intPlusRightIdentity (NegS (S k)) = Refl


export
intPlusLeftIdentity : (a : PInteger) -> 0 + a = a
intPlusLeftIdentity (Pos k) = Refl
intPlusLeftIdentity (NegS k) = Refl

distirbuteNegation_rhs_8 : (a : Nat) -> (b : Nat) -> neg (NegS a + Pos (S b)) = Pos (S a) + NegS b
distirbuteNegation_rhs_8 0 b = case b of { 0 => Refl ; S k => Refl }
distirbuteNegation_rhs_8 (S k) 0 = case k of { 0 => Refl ; S k => Refl }
distirbuteNegation_rhs_8 (S k) (S j) = distirbuteNegation_rhs_8 k j

distirbuteNegation_rhs_7 : (k : Nat) -> (b : Nat) -> neg (Pos (S k) + NegS b) = NegS k + Pos (S b)
distirbuteNegation_rhs_7 0 b = case b of { 0 => Refl ; S k => Refl }
distirbuteNegation_rhs_7 (S k) 0 = case k of { 0 => Refl ; S k => Refl }
distirbuteNegation_rhs_7 (S k) (S j) = distirbuteNegation_rhs_7 k j

export 
distributeNegation : (a,b : PInteger) -> -(a + b) = -a + -b
distributeNegation (Pos 0) (Pos b) =  rewrite intPlusLeftIdentity (neg (Pos b)) in Refl
distributeNegation (Pos (S k)) (Pos 0) = 
  rewrite plusZeroRightNeutral k in 
  rewrite intPlusRightIdentity (NegS k)  in
  Refl
distributeNegation (Pos (S a)) (Pos (S b)) = 
  rewrite combineNegAdd a b in
  rewrite plusSuccRightSucc a b in
  Refl
distributeNegation (Pos 0) (NegS b) = Refl
distributeNegation (NegS a) (Pos (S b)) = distirbuteNegation_rhs_8 a b
distributeNegation (Pos (S k)) (NegS b) = distirbuteNegation_rhs_7 k b
distributeNegation (NegS a) (Pos 0) = 
  rewrite plusZeroRightNeutral a in 
  rewrite intPlusRightIdentity (NegS a)  in
  Refl
distributeNegation (NegS a) (NegS b) = 
  rewrite combineNegAdd a b in
  rewrite plusSuccRightSucc a b in
  Refl

