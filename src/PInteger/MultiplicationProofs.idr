module PInteger.MultiplicationProofs

import PInteger
import PInteger.AdditionProofs
import Data.Nat

%default total

export
intMultLeftZero : (a : PInteger) -> 0 * a = 0
intMultLeftZero (Pos k) = Refl
intMultLeftZero (NegS k) = Refl

export
distributeNegLeft : (a,b : PInteger) -> -a * b = -(a * b)
distributeNegLeft (Pos 0) (Pos b) = Refl
distributeNegLeft (Pos (S k)) (Pos b) = Refl
distributeNegLeft (Pos 0) (NegS b) = Refl
distributeNegLeft (Pos (S k)) (NegS b) = Refl
distributeNegLeft (NegS a) (Pos 0) = rewrite multZeroRightZero a in Refl
distributeNegLeft (NegS a) (Pos (S k)) = Refl
distributeNegLeft (NegS a) (NegS b) = Refl

export
swapSigns : (a,b : PInteger) -> -a * b = a * -b
swapSigns (Pos 0) (Pos b) = rewrite intMultLeftZero (-(Pos b)) in Refl
swapSigns (Pos (S k)) (Pos 0) = rewrite multZeroRightZero k in Refl
swapSigns (Pos (S k)) (Pos (S j)) = Refl
swapSigns (Pos 0) (NegS b) = Refl
swapSigns (Pos (S k)) (NegS b) = Refl
swapSigns (NegS a) (Pos 0) = rewrite multZeroRightZero a in Refl
swapSigns (NegS a) (Pos (S k)) = Refl
swapSigns (NegS a) (NegS b) = Refl

export
distributeNegRight : (a,b : PInteger) -> a * -b = -(a * b)
distributeNegRight a b = rewrite sym $ swapSigns a b in distributeNegLeft a b

export
intMultCommutative : (a,b : PInteger) -> a * b = b * a
intMultCommutative (Pos a) (Pos b) = rewrite multCommutative a b in Refl
intMultCommutative (NegS a) (NegS b) = rewrite multCommutative (S a) (S b) in Refl
intMultCommutative (NegS a) (Pos b) = 
  rewrite multRightSuccPlus b a in
  rewrite multCommutative a b in
  Refl
intMultCommutative (Pos a) (NegS b) = 
  rewrite multRightSuccPlus a b in
  rewrite multCommutative a b in
  Refl

export
doubleNeg : (a : PInteger) -> -(-a) = a
doubleNeg (Pos k) = case k of { 0 => Refl ; S k => Refl }
doubleNeg (NegS k) = Refl

export
intMultAssociative : (a,b,c : PInteger) -> a * (b * c) = (a * b) * c
intMultAssociative (Pos a) (Pos b) (Pos c) = 
  rewrite multAssociative a b c in 
  Refl
intMultAssociative (Pos a) (Pos b) (NegS c) = 
  rewrite distributeNegRight (Pos a) (Pos (b * S c)) in
  rewrite multAssociative a b (S c) in
  Refl
intMultAssociative (Pos a) (NegS b) (Pos c) = 
  rewrite distributeNegRight (Pos a) (Pos (S b * c)) in
  rewrite distributeNegLeft (Pos (a * S b)) (Pos c) in
  rewrite multAssociative a (S b) c in
  Refl
intMultAssociative (Pos a) (NegS b) (NegS c) = 
  rewrite distributeNegLeft (Pos (a * S b)) (NegS c) in
  rewrite multAssociative a (S b) (S c) in
  rewrite doubleNeg (Pos ((a * S b) * S c)) in
  Refl
intMultAssociative (NegS a) (Pos b) (Pos c) = 
  rewrite distributeNegLeft (Pos (S a * b)) (Pos c) in 
  rewrite multAssociative (S a) b c in
  Refl
intMultAssociative (NegS a) (Pos b) (NegS c) = 
  rewrite distributeNegLeft (Pos (S a * b)) (NegS c) in
  rewrite distributeNegRight (NegS a) (Pos (b * S c)) in
  rewrite multAssociative (S a) b (S c) in
  Refl
intMultAssociative (NegS a) (NegS b) (Pos c) = 
  rewrite distributeNegRight (NegS a) (Pos (S b * c)) in
  rewrite doubleNeg (Pos (S a * (S b * c))) in
  rewrite multAssociative (S a) (S b) c in
  Refl
intMultAssociative (NegS a) (NegS b) (NegS c) = 
  rewrite multAssociative (S a) (S b) (S c) in 
  Refl

export
intMultLeftNeutral : (a : PInteger) -> 1 * a = a
intMultLeftNeutral (Pos k) = rewrite plusZeroRightNeutral k in Refl
intMultLeftNeutral (NegS k) = rewrite plusZeroRightNeutral k in Refl

export
intMultLeftNegate : (a : PInteger) -> -1 * a = -a
intMultLeftNegate (Pos k) = rewrite plusZeroRightNeutral k in Refl
intMultLeftNegate (NegS k) = rewrite plusZeroRightNeutral k in Refl

export
intMultLeftSuccPlusPos : (a : Nat) -> (b : PInteger) -> Pos (S a) * b = b + (Pos a * b)
intMultLeftSuccPlusPos 0 b = 
  rewrite intMultLeftNeutral b in
  rewrite intMultLeftZero b in
  rewrite intPlusRightNeutral b in
  Refl
intMultLeftSuccPlusPos (S a) (Pos k) = Refl
intMultLeftSuccPlusPos (S a) (NegS k) = 
  rewrite combineNegAdd k (k + (a * S k)) in
  rewrite plusSuccRightSucc k (k + a * S k) in
  Refl

intMultDistributivePos : (a : Nat) -> (b,c : PInteger) -> Pos a * (b + c) = (Pos a * b) + (Pos a * c)
intMultDistributivePos 0 b c = 
  rewrite intMultLeftZero b in
  rewrite intMultLeftZero c in
  rewrite intMultLeftZero (b + c) in
  Refl
intMultDistributivePos (S a) b c = 
  rewrite intMultLeftSuccPlusPos a (b + c) in
  rewrite intMultLeftSuccPlusPos a b in
  rewrite intMultLeftSuccPlusPos a c in
  rewrite intMultDistributivePos a b c in
  rewrite sym $ intPlusAssociative b (Pos a * b) (c + (Pos a * c)) in
  rewrite intPlusAssociative (Pos a * b) c (Pos a * c) in
  rewrite intPlusCommutative (Pos a * b) c in
  rewrite intPlusAssociative b (c + (Pos a * b)) (Pos a * c) in
  rewrite intPlusAssociative b c (Pos a * b) in
  rewrite sym $ intPlusAssociative (b + c) (Pos a * b) (Pos a * c) in
  Refl

export
intMultLeftSuccPlusNeg : (a : Nat) -> (b : PInteger) -> NegS (S a) * b = (-b) + (NegS a * b)
intMultLeftSuccPlusNeg a (Pos b) = rewrite distributeNegation (Pos b) (Pos (S a * b)) in Refl
intMultLeftSuccPlusNeg a (NegS b) = Refl

intMultDistributiveNeg : (a : Nat) -> (b,c : PInteger) -> NegS a * (b + c) = (NegS a * b) + (NegS a * c)
intMultDistributiveNeg 0 b c = 
  rewrite intMultLeftNegate (b + c) in
  rewrite intMultLeftNegate b in
  rewrite intMultLeftNegate c in
  rewrite distributeNegation b c in
  Refl
intMultDistributiveNeg (S a) b c = 
  rewrite intMultLeftSuccPlusNeg a (b + c) in
  rewrite intMultLeftSuccPlusNeg a b in
  rewrite intMultLeftSuccPlusNeg a c in
  rewrite intMultDistributiveNeg a b c in
  rewrite sym $ intPlusAssociative (-b) (NegS a * b) (-c + (NegS a * c)) in
  rewrite intPlusAssociative (NegS a * b) (-c) (NegS a * c) in
  rewrite intPlusCommutative (NegS a * b) (-c) in
  rewrite intPlusAssociative (-b) (-c + (NegS a * b)) (NegS a * c) in
  rewrite intPlusAssociative (-b) (-c) (NegS a * b) in
  rewrite sym $ intPlusAssociative (-b + -c) (NegS a * b) (NegS a * c) in
  rewrite distributeNegation b c in
  Refl

export
intMultDistributive : (a,b,c : PInteger) -> a * (b + c) = (a * b) + (a * c)
intMultDistributive (Pos a) b c = intMultDistributivePos a b c
intMultDistributive (NegS a) b c = intMultDistributiveNeg a b c
