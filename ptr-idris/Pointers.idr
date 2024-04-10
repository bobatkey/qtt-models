module Pointers

Word : Type
Word = Bits64

%extern
eqWord : (x : Word) -> (y : Word) -> Dec (x = y)

%extern
PtsTo : Word -> Word -> Type -- FIXME: should be 'LType'

%extern
read : (loc : Word) -> {0 v : Word} -> (1 _ : PtsTo loc v) -> (v' ** (v = v', PtsTo loc v'))

%extern
write : (loc : Word) -> {0 v : Word} -> (v' : Word) -> (1 _ : PtsTo loc v) -> PtsTo loc v'

0
Rep : Type -> Type
Rep a = Word -> a -> Word -> Type -- FIXME: should be 'LType'

-- The idea is that a predicate rep : Rep a describes a way to
-- represent values of type 'a' stored in memory at a particular
-- location with a distinguished 'next' pointer.

-- Perhaps 'Rep' should be a record that also includes the 'getNext'
-- operation from below?

0
WordR : Rep Word
WordR begin w end = (PtsTo begin w, end = begin + 1)

-- FIXME: the 'm' should be erased in the next three entries.
0
PairR : Rep a -> Rep b -> Rep (a,b)
PairR repA repB s (a, b) e = (m : Word ** (repA s a m, repB m b e))

0
DPairR : {0 a : Type} -> {0 b : a -> Type} ->
         Rep a -> ((x : a) -> Rep (b x)) -> Rep (x : a ** b x)
DPairR repA repB s (x ** y) e = (m : Word ** (repA s x e, repB x m y e))

0
PairR_ : Rep a -> Rep () -> Rep a
PairR_ repA repU s a e = (m : Word ** (repA s a m, repU m () e))

0
Link : Rep ()
Link s _ e = PtsTo s e

------------------------------------------------------------------------------
-- Sequential data representations

data ListR : (r : Rep a) -> Rep (List a) where
  Nil  : ListR r l [] l
  Cons : {0 r : Rep a} ->
         {0 m : Word} ->
         (0 _ : Not (s = e)) ->
         r s x m ->
         ListR r m xs e ->
         ListR r s (x :: xs) e

invertNil : (1 _ : ListR repA s xs s) -> xs = []
invertNil Nil               = Refl
invertNil (Cons notEnd _ _) = void (notEnd Refl)

data ConsView : Rep a -> Rep (List a) where
  MkConsView : {0 r : Rep a} ->
               {0 m : Word} ->
               {0 x : a} ->
               {0 xs : List a} ->
               r s x m ->
               ListR r m xs e ->
               ConsView r s (x :: xs) e

invertCons : (0 _ : Not (s = e)) ->
             (1 _ : ListR repA s xs e) ->
             ConsView repA s xs e
invertCons neq Nil = void (neq Refl)
invertCons neq (Cons _ xR xsR) = MkConsView xR xsR

-- Maybe we'll need an axiom like "PtsTo x _ * PtsTo y _ -> Not (x =
-- y)", but this would require a realisability type?

{-
-- need a proof that 'e' is not in the first list to avoid circularity.
--
-- if 'rep' is fixed size, then this ought to be automatic
appendListR : ListR rep s xs m -> ListR rep m ys e -> ListR rep s (xs ++ ys) e
appendListR Nil               ysR = ysR
appendListR (Cons neq xR xsR) ysR = Cons neq2 xR (appendListR xsR ysR)
  where neq2 : Not (s = e)
        neq2 eq = ?prf
-}

------------------------------------------------------------------------------

data Erased : Type -> Type where
  Erase : (0 _ : a) -> Erased a

------------------------------------------------------------------------------
-- Fixed jump things

0
FixedJump : Rep a -> Type
FixedJump repA =
  (size : Word **
    Erased ({0 s : Word} ->
            {0 e : Word} ->
            {0 x : a} ->
            (0 _ : repA s x e) ->
            e = s + size))

FixedJump_Word : FixedJump WordR
FixedJump_Word = (1 ** Erase (\wordR => case wordR of (_, Refl) => Refl))

%extern
assoc : {0 z : Word} -> (x + y) + z = x + (y + z)

FixedJump_Pair : FixedJump repA -> FixedJump repB -> FixedJump (PairR repA repB)
FixedJump_Pair (size1 ** Erase evidence1) (size2 ** Erase evidence2) =
  (size1 + size2 ** Erase evidence)
  where 0 evidence : {0 x : _} ->
                     (0 _ : PairR repA repB s x e) -> e = s + (size1 + size2)
        evidence {x = (x , y)} (m ** (xR , yR)) =
          case evidence1 xR of
            Refl => case evidence2 yR of
              Refl => assoc



------------------------------------------------------------------------------
-- Specification of being able to get the “next” pointer from a
-- representation.
0
GetNext : Rep a -> Type
GetNext repA =
  (s : Word) ->
  {0 e : Word} ->
  {0 x : a} ->
  (1 _ : repA s x e) ->
  (e' ** (e = e', repA s x e))

-- GetNext_Word

------------------------------------------------------------------------------
-- Being able to update the “next” pointer of a representation.
0
UpdateNext : Rep a -> Type
UpdateNext repA =
  (s : Word) ->
  {0 e : Word} ->
  (e' : Word) ->
  {0 x : a} ->
  (1 _ : repA s x e) ->
  repA s x e'

UpdateNext_Link : UpdateNext Link
UpdateNext_Link s e' ptsto = write s e' ptsto

-- UpdateNext_PairR_ : UpdateNext (PairR_ repA repU)
-- UpdateNext_PairR_ = ?foop

------------------------------------------------------------------------------
-- Update in-place specification
0
Updater : {a : Type} -> Rep a -> (a -> b) -> Rep b -> Type
Updater {a} repA f repB =
  (s : Word) -> (e : Word) -> {0 x : a} -> (1 _ : repA s x e) -> repB s (f x) e



------------------------------------------------------------------------------
-- Reading some "stack data" from a representation
0
Reader : {a : Type} -> Rep a -> (a -> b) -> Type
Reader {a} repA f =
  (s : Word) ->
  {0 e : Word} ->
  {0 x : a} ->
  (1 _ : repA s x e) ->
  (y : b ** (y = f x, repA s x e))


------------------------------------------------------------------------------
-- Some generic algorithms on sequential data

-- If it is possible to update an element in place, and it is possible
-- to advance to the next element, then it is possible to update a
-- list of elements.
inplaceMap : GetNext repA ->
             Updater repA f repB ->
             Updater (ListR repA) (map f) (ListR repB)
inplaceMap next updateElem iter end repList =
  case eqWord iter end of
    Yes Refl =>
      case invertNil repList of
        Refl => Nil
    No neq =>
      case invertCons neq repList of
        MkConsView xR xsR =>
          case next iter xR of
            (iter' ** (Refl, xR)) =>
              let yR  = updateElem iter iter' xR
                  ysR = inplaceMap next updateElem iter' end xsR
              in Cons neq yR ysR

discard : (a -> Bool) -> List a -> List a
discard predicate xs = filter (not . predicate) xs

-- FIXME: this is not tail-recursive
partition : GetNext rep ->
            UpdateNext rep ->
            Reader rep predicate ->
            (begin : Word) ->
            (end : Word) ->
            (1 _ : ListR rep begin xs end) ->
            (begin1 : Word **
             (begin2 : Word **
               (ListR rep begin1 (filter predicate xs) end,
                ListR rep begin2 (discard predicate xs) end)))
partition getNext updNext predImpl node end repList =
  case eqWord node end of
    Yes Refl =>
      case invertNil repList of
        Refl => (node ** (node ** (Nil, Nil)))
    No neq =>
      case invertCons neq repList of
        MkConsView xR xsR =>
          case getNext node xR of
            (iter ** (Refl, xR)) =>
              case partition getNext updNext predImpl iter end xsR of
                (node1 ** (node2 ** (yesR, noR))) =>
                  case predImpl node xR of
                    (True ** (eq, xR)) =>
                      let xR' = updNext node node1 xR in
                      rewrite sym eq in
                      (node ** (node2 ** (Cons neq xR' yesR, noR)))
                    (False ** (eq, xR)) =>
                      let xR' = updNext node node2 xR in
                      rewrite sym eq in
                      (node1 ** (node ** (yesR, Cons neq xR' noR)))

-- TODO:
-- 1. tail recursive partiion
-- 2. in-place reverse
-- 3. findFirst
-- 4.
