module Pointers

import Data.Singleton

data DLPair : (a : Type) -> (b : a -> Type) -> Type where
  ( #> ) : (x : a) -> (1 _ : b x) -> DLPair a b

data ELPair : (a : Type) -> (b : a -> Type) -> Type where
  ( ## ) : (0 x : a) -> (1 _ : b x) -> ELPair a b

private infix 10 ##

private infixr 10 #>

------------------------------------------------------------------------------

Word : Type
Word = Bits64

%extern
eqWord : (x : Word) -> (y : Word) -> Dec (x = y)

%extern
PtsTo : Word -> Word -> Type -- FIXME: should be 'LType'

%extern
read : (loc : Word) ->
       {0 v : Word} ->
       (1 _ : PtsTo loc v) ->
       DLPair Word (\w => DLPair (w = v) (\_ => PtsTo loc v))

%extern
write : (loc : Word) ->
        {0 v : Word} ->
        (v' : Word) ->
        (1 _ : PtsTo loc v) ->
        PtsTo loc v'

------------------------------------------------------------------------------
-- postulate a memory allocator monad

%extern
AllocM : Type -> Type

%extern
return : a -> AllocM a

%extern
bind : AllocM a -> (a -> AllocM b) -> AllocM b

-- FIXME: this allocates but a single word
%extern
malloc : AllocM (DLPair Word (\w => ELPair Word (\w' => PtsTo w w')))

-- Going to need a type that represents a malloc'd block of memory, so
-- that when the memory is free'd, we know what to do with it.

------------------------------------------------------------------------------
0
Rep : Type -> Type
Rep a = Word -> a -> Word -> Type -- FIXME: should be 'LType'

-- The idea is that a predicate 'rep : Rep a' describes a way to
-- represent values of type 'a' stored in memory at a particular
-- location with a distinguished 'next' pointer.

-- Perhaps 'Rep' should be a record that also includes the 'getNext'
-- operation from below?

------------------------------------------------------------------------------
0
WordR : Rep Word
WordR begin w end = DLPair (end = begin + 1) (\_ => PtsTo begin w)

mkWordR : (1 _ : PtsTo loc w) -> WordR loc w (loc + 1)
mkWordR ptsto = Refl #> ptsto

0
PairR : Rep a -> Rep b -> Rep (a,b)
PairR repA repB s (a, b) e = ELPair Word (\m => LPair (repA s a m) (repB m b e))

0
DPairR : {0 a : Type} -> {0 b : a -> Type} ->
         Rep a -> ((x : a) -> Rep (b x)) -> Rep (x : a ** b x)
DPairR repA repB s (x ** y) e = ELPair Word (\m => LPair (repA s x e) (repB x m y e))

0
PairR_ : Rep a -> Rep () -> Rep a
PairR_ repA repU s a e = ELPair Word (\m => LPair (repA s a m) (repU m () e))

0
Link : Rep ()
Link s _ e = PtsTo s e

------------------------------------------------------------------------------
-- Sequential data representations

data ListR : (r : Rep a) -> Rep (List a) where
  Nil  : ListR r l [] l
  Cons : (0 _ : Not (s = e)) ->
         (1 _ : r s x m) ->
         (1 _ : ListR r m xs e) ->
         ListR r s (x :: xs) e

-- Idris will not stop us from pattern matching directly on 'ListR'
-- values, but really they should be erased and we have to indirectly
-- access them by first asking whether the 'begin' and 'end' pointers
-- are equal.

invertNil : (1 _ : ListR repA s xs s) -> xs = []
invertNil Nil               = Refl
invertNil (Cons notEnd x y) =
  -- FIXME: this is a bit of a mess. Is there a better way?
  the ((1 _ : _) -> xs = []) (void (notEnd Refl)) (x # y)

data ConsView : Rep a -> Rep (List a) where
  MkConsView : {0 r : Rep a} ->
               {0 m : Word} ->
               {0 x : a} ->
               {0 xs : List a} ->
               (1 _ : r s x m) ->
               (1 _ : ListR r m xs e) ->
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
FixedJump_Word = (1 ** Erase (\wordR => case wordR of (Refl #> _) => Refl))

%extern
assoc : {0 z : Word} -> (x + y) + z = x + (y + z)

FixedJump_Pair : FixedJump repA -> FixedJump repB -> FixedJump (PairR repA repB)
FixedJump_Pair (size1 ** Erase evidence1) (size2 ** Erase evidence2) =
  (size1 + size2 ** Erase evidence)
  where 0 evidence : {0 x : _} ->
                     (0 _ : PairR repA repB s x e) -> e = s + (size1 + size2)
        evidence {x = (x , y)} (m ## (xR # yR)) =
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
  DLPair Word (\w => DLPair (w = e) (\_ => repA s x e))

GetNext_Link : GetNext Link
GetNext_Link loc ptsto = read loc ptsto

GetNext_Word : GetNext WordR
GetNext_Word s (Refl #> ptsto) = (s + 1) #> Refl #> Refl #> ptsto

GetNext_Pair : GetNext repA -> GetNext repB -> GetNext (PairR repA repB)
GetNext_Pair getNextA getNextB s {x = (x, y)} (m ## (xR # yR)) =
  case getNextA s xR of
    m #> Refl #> xR =>
      case getNextB m yR of
        e #> Refl #> yR =>
          e #> Refl #> (m ## (xR # yR))

GetNext_Pair_ : GetNext repA -> GetNext repB -> GetNext (PairR_ repA repB)
GetNext_Pair_ getNextA getNextB s (m ## (xR # yR)) =
  case getNextA s xR of
    m #> Refl #> xR =>
      case getNextB m yR of
        e #> Refl #> yR =>
          e #> Refl #> (m ## (xR # yR))

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
Updater : Rep a -> (a -> b) -> Rep b -> Type
Updater repA f repB =
  (s : Word) -> (e : Word) -> {0 x : a} -> (1 _ : repA s x e) -> repB s (f x) e

updateWord : (f : Word -> Word) -> Updater WordR f WordR
updateWord f s _ {x} (Refl #> ptsto) =
  case read s ptsto of
    w #> eqw #> ptsto =>
      rewrite sym (the (w = x) eqw) in
      Refl #> write s (f w) ptsto

------------------------------------------------------------------------------
-- Set in-place specification. This is a relation between
-- representations because we might be able to change the
-- representation.
0
Setter : Rep a -> Rep b -> Type
Setter repA repB =
  (s : Word) -> {0 e : Word} -> {0 x : a} -> (y : b) -> (1 _ : repA s x e) -> repB s y e

------------------------------------------------------------------------------
-- Reading some "stack data" from a representation
0
Reader : {a : Type} -> Rep a -> (a -> b) -> Type
Reader {a} repA f =
  (s : Word) ->
  {0 e : Word} ->
  {0 x : a} ->
  (1 _ : repA s x e) ->
  LPair (y : b ** y = f x) (repA s x e)


-- FIXME: should be able to build an updater from a Reader and a Setter

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
            iter' #> Refl #> xR =>
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
            DLPair (Word, Word) (\p =>
              LPair (ListR rep (fst p) (filter predicate xs) end)
                    (ListR rep (snd p) (discard predicate xs) end))
partition getNext updNext predImpl node end repList =
  case eqWord node end of
    Yes Refl =>
      case invertNil repList of
        Refl => ((node, node) #> (Nil # Nil))
    No neq =>
      case invertCons neq repList of
        MkConsView xR xsR =>
          case getNext node xR of
            iter #> Refl #> xR =>
              case partition getNext updNext predImpl iter end xsR of
                (node1, node2) #> (yesR # noR) =>
                  case predImpl node xR of
                    (True ** eq) # xR =>
                      let xR' = updNext node node1 xR in
                      rewrite sym eq in
                      (node, node2) #> (Cons neq xR' yesR # noR)
                    (False ** eq) # xR =>
                      let xR' = updNext node node2 xR in
                      rewrite sym eq in
                      (node1, node) #> (yesR # Cons neq xR' noR)

------------------------------------------------------------------------------
-- In-place reversal of linked lists

{- List reverse:

   node *reverse(node *list, node *end) {
     node *ptr = NULL;
     while (list != end) {
       node *tmp = list->next;
       list->next = ptr;
       ptr = list;
     }
     return ptr;
  }

-}

-- if we can update the next pointer of each element, then we get an
-- in-place sequence reversal.
reverseOntoR : GetNext rep ->
               UpdateNext rep ->
               (iter : Word) ->
               (end : Word) ->
               (ptr : Word) ->
               (1 _ : ListR rep ptr xs end) ->
               (1 _ : ListR rep iter ys end) ->
               DLPair Word (\w => ListR rep w (reverseOnto xs ys) end)
reverseOntoR getNext setNext iter end ptr xsR ysR =
  case eqWord iter end of
    Yes Refl =>
      case invertNil ysR of
        Refl => ptr #> xsR
    No neq =>
      case invertCons neq ysR of
        MkConsView yR ysR =>
          case getNext iter yR of
            next #> Refl #> yR =>
              let yR = setNext iter ptr yR in
              reverseOntoR getNext setNext next end iter (Cons neq yR xsR) ysR

reverseR : GetNext rep ->
           UpdateNext rep ->
           (begin : Word) ->
           (end : Word) ->
           (1 _ : ListR rep begin xs end) ->
           DLPair Word (\w => ListR rep w (reverse xs) end)
reverseR getNext setNext begin end xsR =
  reverseOntoR getNext setNext begin end end Nil xsR

------------------------------------------------------------------------------

-- TODO:
-- 1. tail recursive partition
-- 2. quicksort on lists of fixed size representations
-- 3. findFirst, that splits the list
-- 4. hashtables, and possibly trees.
-- 5. Memory allocator monad
