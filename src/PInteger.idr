module PInteger

import Data.Nat

%default total

public export 
data PInteger : Type where
  Pos : Nat -> PInteger
  Neg : Nat -> PInteger

export 
getNat : PInteger -> Nat
getNat (Pos n) = n
getNat (Neg n) = n

export 
Show PInteger where
  show (Pos n) = show n
  show (Neg n) = "-" ++ show n

export 
pos0_neg0_equality : Pos Z = Neg Z
pos0_neg0_equality = believe_me ()
  -- Neg Z and Pos Z arent defined with the same construction 
  -- so it's impossible to infer that they are equal

export 
Num PInteger where
  fromInteger x = case compareInteger x 0 of 
                       GT => Pos (fromInteger x)
                       EQ => Pos 0
                       LT => Neg (fromInteger (-x))
  n1 + Pos Z = n1
  n1 + Neg Z = n1
  Pos Z + n2 = n2
  Neg Z + n2 = n2

  Pos n1 + Pos n2 = Pos (n1 + n2)
  Neg n1 + Neg n2 = Neg (n1 + n2)

  -- I don't know why this isnt recognized as total
  Neg (S n1) + Pos (S n2) = Neg n1 + assert_smaller (Pos (S n2)) (Pos n2)
  Pos (S n1) + Neg (S n2) = Pos n1 + assert_smaller (Neg (S n2)) (Neg n2)

  Pos 0 * x = Pos 0
  Neg 0 * x = Pos 0
  x * Pos 0 = Pos 0
  x * Neg 0 = Pos 0

  Pos 1 * x = x
  x * Pos 1 = x

  Neg 1 * Pos x = Neg x
  Neg 1 * Neg x = Pos x

  Pos x * Neg 1 = Neg x
  Neg x * Neg 1 = Pos x

  x * Pos (S k) = x + (x * assert_smaller (Pos (S k)) (Pos k))
  Pos j * Neg (S k) = assert_total $ Neg j + (Pos j * Neg k)
  Neg j * Neg k = assert_total $ Pos j * Pos k

export 
Neg PInteger where
  negate (Pos x) = Neg x
  negate (Neg x) = Pos x
  x - y = x + negate y

export 
Abs PInteger where
  abs (Neg x) = Pos x
  abs x = x

export 
Integral PInteger where
  div (Pos k) (Pos j) = Pos (div k j)
  div (Pos k) (Neg j) = Neg (div k j)
  div (Neg k) (Pos j) = Neg (div k j)
  div (Neg k) (Neg j) = Pos (div k j)
  mod x y = Pos (getNat x `mod` getNat y)

export 
integerToEither : PInteger -> Either Nat Nat
integerToEither (Neg s) = Left s
integerToEither (Pos s) = Right s
