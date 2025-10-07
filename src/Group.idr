interface (Monoid x) => Group (x : Type) where
    invert : x -> x
    identity : (a : x) ->  (a <+> Prelude.Interfaces.neutral = a, Prelude.Interfaces.neutral <+> a = a)
    inverse : (a : x) -> (a <+> (invert a) = Prelude.Interfaces.neutral)
    associativity : (a, b, c : x) -> (a <+> b) <+> c = a <+> (b <+> c)

interface Group x => AbelianGroup (x : Type) where
    commutativity : (a, b : x) -> a <+> b = b <+> a
