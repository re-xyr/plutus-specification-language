{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Ledger where

data PubKey
data Signature

newtype POSIXTime = POSIXTime {getPOSIXTime :: Integer} deriving (Eq, Ord, Num)
newtype Slot = Slot {getSlot :: Integer} deriving (Eq, Ord, Num)

type SlotRange = Interval Slot
type POSIXTimeRane = Interval POSIXTime

data Interval a

always :: Interval a
always = undefined

newtype Value = Value {getValue :: Map CurrencySymbol (Map TokenName Integer)}
newtype Map k v = Map { unMap :: [(k, v)] }

data CurrencySymbol
data TokenName
