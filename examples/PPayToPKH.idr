module PPayToPKH

import PSL
import Data.Nat
import Data.DPair

pPayToPKHPermissible : (self : ProtocolName d) -> (PubKeyHash, TimeRange) -> TxDiagram {d} self
pPayToPKHPermissible self (pkh, validRange) = MkTxDiagram {
  inputs = Nil,
  outputs = Nil,
  mint = NilMap,
  signatures = [pkh],
  validRange = validRange
}

pPayToPKH : Protocol
pPayToPKH = MkProtocol {
  datumType = PubKeyHash,
  permissible' = \self => MkSet (the Type (PubKeyHash, TimeRange)) (pPayToPKHPermissible self)
}
