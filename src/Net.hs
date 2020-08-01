{-# LANGUAGE MultiWayIf #-}
module Net where

import           Control.Monad.State.Strict
import           Data.List                  (intercalate)
import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import qualified Data.Vector.Unboxed        as V
import           Data.Word
import           Data.Bits
import           Numeric     (showHex)
import           Text.Printf (PrintfArg, printf)

type Node = (Word64, Word64, Word64, Word64)

nodeInfo :: Node -> Word64
nodeInfo (i,p,l,r) = i

mainPort :: Node -> Word64
mainPort (i,m,l,r) = m

leftPort  :: Node -> Word64
leftPort (i,m,l,r) = l

rightPort :: Node -> Word64
rightPort (i,m,l,r) = r

showPort :: Slot -> Word64 -> String
showPort M n = "M" ++ showHex n ""
showPort L n = "L" ++ showHex n ""
showPort R n = "R" ++ showHex n ""

showNode :: (Integer,Node) -> String
showNode (x,(i,m,l,r)) = case readInfoBits i of
  (Info mS lS rS k) -> concat 
    [show x,":",show k,"_",showPort mS m,showPort lS l,showPort rS r]

i64_truncate :: Word64 -> Word32
i64_truncate n = (fromIntegral n) .&. 0xFFFFFFFF

data Slot
  = M -- Main
  | L -- Left
  | R -- Right
  deriving (Enum, Show, Bounded, Eq, Ord)

type Kind = Word32

data Info = Info
  { _mainSlot  :: Slot
  , _leftSlot  :: Slot
  , _rightSlot :: Slot
  , _kind      :: Kind
  } deriving Eq

-- infoBits layout:
-- | 2 mainSlot | 2 leftSlot | 2 rightSlot | 26 unused | 32 kind |
infoBits :: Info -> Word64
infoBits (Info main left rigt kind)  = fromIntegral $
  (fromEnum main) `shiftL` 62 +
  (fromEnum left) `shiftL` 60 +
  (fromEnum rigt) `shiftL` 58 +
  (fromEnum kind)

readInfoBits :: Word64 -> Info
readInfoBits x = let n = (fromIntegral x) in Info
  (toEnum $ (n `shiftR` 62) .&. 0x3)
  (toEnum $ (n `shiftR` 60) .&. 0x3)
  (toEnum $ (n `shiftR` 58) .&. 0x3)
  (toEnum $ n .&. 0x00000000FFFFFFFF)

instance Enum Info where
  toEnum = readInfoBits . fromIntegral
  fromEnum = fromIntegral . infoBits

instance Show Info where
  show (Info m l r k) = concat [show k, ":", show m, show l, show r]

printBits :: (PrintfArg a) => a -> IO ()
printBits n = do
  putStrLn $ printf "%08b" n

mkNode :: Kind -> (Slot,Word64) -> (Slot,Word64) -> (Slot,Word64) -> Node
mkNode k (mS,m) (lS,l) (rS,r) = (infoBits (Info mS lS rS k),m,l,r)

mkFree :: Word64 -> Node
mkFree i = (infoBits (Info M L R 0),i,i,i)

mkSet  :: Slot -> Word64 -> Node
mkSet s n = (infoBits (Info L s L 0),0,n,0)

getKind :: Node -> Kind
getKind (i,_,_,_) = _kind $ readInfoBits i

data Net =
  Net { _nodes :: V.Vector Node
      , _freed :: [Word64]
      , _redex :: [(Word64,Word64)]
      } deriving Eq

instance Show Net where
  show (Net ws fs rs) = concat $
      [ intercalate "\n" (showNode <$> (zip [0..] (V.toList ws)))
      , "\n"
      , "FREE:", show fs
      , "\n"
      , "REDEX:", show rs
      ]

testNodes :: [Node]
testNodes =
  [ mkNode 1 (M,0) (L,1) (L,0)
  -- , Node (labelBits (Label True Con M R R)) 0 1 1
  , mkNode 1 (M,0) (R,1) (R,1)
  ]

testWords :: V.Vector Node
testWords = V.fromList testNodes

findRedexes :: V.Vector Node -> [(Word64, Word64)]
findRedexes vs = Set.toList $ V.ifoldr insertRedex Set.empty vs
  where
    insertRedex :: Int -> Node -> Set (Word64, Word64) -> Set (Word64, Word64)
    insertRedex i (b,m,l,r) set
      |    _mainSlot (readInfoBits b) == M
        && _mainSlot (readInfoBits b') == M
        && i == fromIntegral m'
        && not (Set.member (m,m') set)
        = Set.insert (m',m) set
      | otherwise = set
        where
         (b',m',l',r')  = vs V.! (fromIntegral m)

makeNet :: [Node] -> Net
makeNet nodes = let vs = V.fromList nodes in Net vs [] (findRedexes vs)

testNet :: Net
testNet = makeNet testNodes

allocNode :: Kind -> State Net Word64
allocNode k = do
  (Net vs fs rs) <- get
  let node i = (infoBits (Info M L R k), i, i, i)
  case fs of
    [] -> do
      let i = fromIntegral (V.length vs)
      modify (\n -> n { _nodes = vs `V.snoc` (node i)})
      return i
    (f:fs) -> do
      modify (\n -> n { _nodes = vs V.// [(fromIntegral f,node f)], _freed = fs})
      return f

isFreed :: Word64 -> State Net Bool
isFreed i = do
  f <- gets _freed
  return $ i `elem` f

freeNode :: Word64 -> State Net ()
freeNode i = do
  let node = (infoBits (Info M L R 0),i,i,i)
  modify (\n ->
    n { _nodes = (_nodes n) V.// [(fromIntegral i,node)]
      , _freed = i:(_freed n)
      })

getNode :: Word64 -> State Net Node
getNode i = (\vs -> vs V.! (fromIntegral i)) <$> gets _nodes

getPort :: Slot -> Node -> (Slot, Word64)
getPort s (b,m,l,r) =
  let i = readInfoBits b in
  case s of
    M ->  (_mainSlot  i,m)
    L ->  (_leftSlot  i,l)
    R ->  (_rightSlot i,r)

enterPort :: (Slot, Word64) -> State Net (Slot,Word64)
enterPort (s, n) = do
  node <- getNode n
  return $ (getPort s node)

setSlot :: Node -> Slot -> (Slot, Word64) -> Node
setSlot node@(b,m,l,r) x (s,n)  =
  let i = readInfoBits b in
  case x of
  M -> (infoBits $ i { _mainSlot = s }, n, l, r)
  L -> (infoBits $ i { _leftSlot = s    }, m, n, r)
  R -> (infoBits $ i { _rightSlot = s   }, m, l, n)

setPort :: Slot -> Word64 -> (Slot,Word64) -> State Net ()
setPort s i port = do
  node <- ((\x -> x V.! (fromIntegral i)) <$> gets _nodes)
  modify $ \n ->
    n { _nodes = (_nodes n) V.// [(fromIntegral i, (setSlot node s port))] }

linkSlots :: (Slot,Word64) -> (Slot, Word64) -> State Net ()
linkSlots (sa,ia) (sb,ib) = do
  setPort sa ia $ (sb,ib)
  setPort sb ib $ (sa,ia)
  when (sa == M && sb == M) $
   modify (\n -> n { _redex = (ia, ib) : _redex n })

linkPorts :: (Slot,Word64) -> (Slot,Word64) -> State Net ()
linkPorts (sa,ia) (sb,ib) = linkSlots (sa,ia) (sb,ib)

unlinkPort :: (Slot,Word64) -> State Net ()
unlinkPort (sa,ia) = do
  (sb,ib) <- enterPort (sa,ia)
  (sa',ia') <- enterPort (sb,ib)
  if (ia' == ia && sa' == sa) then do
      setPort sa ia (sa,ia)
      setPort sb ib (sb,ib)
    else return ()

rewrite :: (Word64, Word64) -> State Net ()
rewrite (iA, iB) = do
  nodes <- gets $ _nodes
  let a = nodes V.! (fromIntegral iA)
  let b = nodes V.! (fromIntegral iB)
  if
    | (getKind a == getKind b) -> do
      aLdest <- enterPort (L,iA)
      bLdest <- enterPort (L,iB)
      linkPorts aLdest bLdest
      aRdest <- enterPort (R,iA)
      bRdest <- enterPort (R,iB)
      linkPorts aRdest bRdest
      return ()
    | otherwise -> do
      iP <- allocNode (getKind b)
      iQ <- allocNode (getKind b)
      iR <- allocNode (getKind a)
      iS <- allocNode (getKind a)
      linkSlots (L,iS) (R,iP)
      linkSlots (R,iR) (L,iQ)
      linkSlots (R,iS) (R,iQ)
      linkSlots (L,iR) (L,iP)
      a1dest <- enterPort (L,iA)
      a2dest <- enterPort (R,iA)
      b1dest <- enterPort (L,iB)
      b2dest <- enterPort (R,iB)
      linkPorts (M,iP) a1dest
      linkPorts (M,iQ) a2dest
      linkPorts (M,iR) b1dest
      linkPorts (M,iS) b2dest
  mapM_ (\x -> unlinkPort (x,iA)) [M,L,R] >> freeNode iA
  unless (iA == iB) (mapM_ (\x -> unlinkPort (x,iB)) [M,L,R] >> freeNode iB)
  return ()

reduce :: Net -> (Net, Int)
reduce x = go (x {_redex = (findRedexes (_nodes x))}) 0
  where
    go n c = case _redex n of
      []   -> (n, c)
      r:rs -> go (execState (rewrite r) (n { _redex = rs })) (c + 1)

inDuplicate :: Net
inDuplicate = makeNet
  [ mkNode 1 (M,1) (L,2) (L,3)
  , mkNode 2 (M,0) (L,4) (L,5)
  , mkSet L 0
  , mkSet R 0
  , mkSet L 1
  , mkSet R 1
  ]

inAnnihilate :: Net
inAnnihilate = makeNet
  [ mkNode 1 (M,1) (L,2) (L,3)
  , mkNode 1 (M,0) (L,4) (L,5)
  , mkSet L 0
  , mkSet R 0
  , mkSet L 1
  , mkSet R 1
  ]

selfAnnihilate :: Net
selfAnnihilate = makeNet
  [ mkNode 1 (M,0) (L,1) (L,2)
  , mkSet L 0
  , mkSet R 0
  ]
