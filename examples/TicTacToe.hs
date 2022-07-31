{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}

module TicTacToe (GameProtocol) where

import GHC.Generics (Generic)
import MonoidDo qualified
import Plutarch.Core
import Plutarch.EType
import Plutarch.PSL

-- TODO: The type system should know that Red/Blue are players
-- so that we can prove that `gameWon` is called by a player
-- and not `Blank`.
data Slot ef = Red | Blue | Blank
  deriving stock (Eq, Generic)
  deriving anyclass (EIsNewtype)

-- Grid of TTT slots
data Grid ef = Rows (ef /$ Row) (ef /$ Row) (ef /$ Row)
  deriving stock (Generic)
  deriving anyclass (EIsNewtype)

data Row ef = Cells (ef /$ Slot) (ef /$ Slot) (ef /$ Slot)
  deriving stock (Generic)
  deriving anyclass (EIsNewtype)

data Pos ef = P0 | P1 | P2
  deriving stock (Generic)
  deriving anyclass (EIsNewtype)

-- -- TODO: Use type-nats so that you can prove that the given
-- -- grid index is correct
-- initState :: Grid
-- initState =
--   fromList
--     [ (0, fromList [(0, Blank), (1, Blank), (2, Blank)])
--     , (1, fromList [(0, Blank), (1, Blank), (2, Blank)])
--     , (2, fromList [(0, Blank), (1, Blank), (2, Blank)])
--     ]

initGrid :: EPSL edsl => Term edsl Grid
initGrid = econ $ Rows row row row
  where
    row = econ $ Cells slot slot slot
    slot = econ Blank

data GameDatum ef = GameDatum
  { state :: ef /$ Grid,
    redPkh :: ef /$ EPubKeyHash,
    bluePkh :: ef /$ EPubKeyHash,
    value :: ef /$ EValue
  }
  deriving stock (Generic)
  deriving anyclass (EIsNewtype)

data Turn ef = Turn {row :: ef /$ Pos, col :: ef /$ Pos}
  deriving stock (Generic)
  deriving anyclass (EIsNewtype)

data GameCase ef where
  GameInit ::
    { redPkh :: ef /$ EPubKeyHash,
      bluePkh :: ef /$ EPubKeyHash,
      value :: ef /$ EValue
    } ->
    GameCase ef
  RedPlay :: {dat :: ef /$ GameDatum, turn :: ef /$ Turn} -> GameCase ef
  BluePlay :: {dat :: ef /$ GameDatum, turn :: ef /$ Turn} -> GameCase ef
  RedWon :: {dat :: ef /$ GameDatum} -> GameCase ef
  BlueWon :: {dat :: ef /$ GameDatum} -> GameCase ef
  deriving stock (Generic)
  deriving anyclass (EIsNewtype)

data GameProtocol

-- eerror is not available; consider using something else to represent impossible
requireCond :: (EPSL edsl, IsEType edsl d) => Bool -> Term edsl (EDiagram d)
requireCond x = if not x then eerror else mempty

data EBool ef = ETrue | EFalse
  deriving stock (Generic)
  deriving anyclass (EIsNewtype)

instance Protocol GameProtocol GameCase GameDatum where
  specification _ =
    Specification \action -> ematch action \case
      GameInit redPkh bluePkh value -> MonoidDo.do
        requireSignature redPkh
        requireSignature bluePkh
        createOwnOutput $ econ $ EOwnUTXO value $ econ $ GameDatum initGrid redPkh bluePkh value
      RedPlay dat turn -> ematch dat \d@GameDatum {redPkh} -> MonoidDo.do
        requireSignature redPkh
        play Red d turn
      BluePlay dat turn -> ematch dat \d@GameDatum {bluePkh} -> MonoidDo.do
        requireSignature bluePkh
        play Blue d turn
      RedWon dat -> ematch dat \d@GameDatum {redPkh, state} -> MonoidDo.do
        ematch (isWin Red state) \case
          EFalse -> eerror
          ETrue -> setWin redPkh d
      BlueWon dat -> ematch dat \d@GameDatum {bluePkh, state} -> MonoidDo.do
        ematch (isWin Blue state) \case
          EFalse -> eerror
          ETrue -> setWin bluePkh d
    where
      play color d@(GameDatum {state, value}) turn = ematch turn \(Turn row col) -> MonoidDo.do
        ematch (getGrid state row col) \x -> requireCond $ x == Blank
        requireOwnInput $ econ $ EOwnUTXO value $ econ d
        createOwnOutput $ econ $ EOwnUTXO value $ econ $ d {state = setGrid color state row col}
      setGrid color grid row col = ematch grid \(Rows r0 r1 r2) -> ematch row \case
        P0 -> econ $ Rows (setGrid' color r0 col) r1 r2
        P1 -> econ $ Rows r0 (setGrid' color r1 col) r2
        P2 -> econ $ Rows r0 r1 (setGrid' color r2 col)
      setGrid' color row col = ematch row \(Cells r0 r1 r2) -> ematch col \case
        P0 -> econ $ Cells (econ color) r1 r2
        P1 -> econ $ Cells r0 (econ color) r2
        P2 -> econ $ Cells r0 r1 (econ color)
      getGrid grid row col = ematch grid \(Rows r0 r1 r2) -> ematch row \case
        P0 -> getGrid' r0 col
        P1 -> getGrid' r1 col
        P2 -> getGrid' r2 col
      getGrid' row col = ematch row \(Cells r0 r1 r2) -> ematch col \case
        P0 -> r0
        P1 -> r1
        P2 -> r2
      isWin color grid =
        foldr
          ( \xs w -> ematch (isWin' color grid xs) \case
              ETrue -> econ ETrue
              EFalse -> w
          )
          (econ EFalse)
          wins
      isWin' color grid xs =
        foldr
          ( \(r, c) w -> ematch (getGrid grid (econ r) (econ c)) \case
              x -> if x == color then w else econ EFalse
          )
          (econ ETrue)
          xs
      wins =
        [ [(P0, P0), (P0, P1), (P0, P2)],
          [(P1, P0), (P1, P1), (P1, P2)],
          [(P2, P0), (P2, P1), (P2, P2)],
          [(P0, P0), (P1, P0), (P2, P0)],
          [(P0, P1), (P1, P1), (P2, P1)],
          [(P0, P2), (P1, P2), (P2, P2)],
          [(P0, P0), (P1, P1), (P2, P2)],
          [(P0, P2), (P1, P1), (P2, P0)]
        ] ::
          [[(Pos ef, Pos ef)]]
      setWin pkh d@GameDatum {value} = MonoidDo.do
        requireOwnInput $ econ $ EOwnUTXO value $ econ d
        createOutput $ toAddress (fromPkh pkh) value $ econ $ undefined

-- specification =
--   Specification @GameDatum @GameCase
--     ( `ematch`
--         \case
--           GameInit dat@GameDatum{..} -> MonoidDo.do
--             requireOwnOutput $ econ $ EOwnUTXO value $ econ dat
--             requireSignature redPkh
--             requireSignature bluePkh
--           RedPlay dat turn -> redPlay dat val turn
--           BluePlay dat turn -> bluePlay dat turn
--           RedWon dat -> redWon dat
--           BlueWon dat -> blueWon dat
--     )
--  where
--   redPlay = gamePlay Red
--   bluePlay = gamePlay Blue
--   gamePlay slot dat@GameDatum{..} (i, j) = MonoidDo.do
--     requireOwnInput $ econ $ EOwnUTXO value $ econ $ dat{state = insert i (insert j Blank $ state ! i) state}
--     requireOwnOutput $ econ $ EOwnUTXO value $ econ $ dat{state = insert i (insert j slot $ state ! i) state}
--   redWon = gameWon Red
--   blueWon = gameWon Blue
--   gameWon slot dat@GameDatum{..} =
--     if checkGameWon state slot
--       then ematch slot \case
--         Blank -> Undefined
--         _ -> requireWon dat value
--       else Undefined
--   requireWon GameDatum{..} = createOutput $ toAddress (fromPkh redPkh) value mempty
--   checkGameWon state slot = foldl (||) (checkRowWon state slot) wins
--   checkRowWon state slot = foldl (&&) $ (slot ==) . (\(i, j) -> state ! i ! j)
--   wins =
--     [ [(0, 0), (0, 1), (0, 2)]
--     , [(1, 0), (1, 1), (1, 2)]
--     , [(2, 0), (2, 1), (2, 2)]
--     , [(0, 0), (1, 0), (2, 0)]
--     , [(0, 1), (1, 1), (2, 1)]
--     , [(0, 2), (1, 2), (2, 2)]
--     , [(0, 0), (1, 1), (2, 2)]
--     , [(0, 2), (1, 1), (2, 0)]
--     ]
