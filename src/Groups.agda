{-# OPTIONS --omega-in-omega --no-pattern-matching #-}

module IST.Groups where

open import IST.Safe.Groups public

open import IST.Base
open SafeImportTools

st-Group : st Group
st-Group = declared-in-safe-module Group

st-Group-Carrier : st Group.Carrier
st-Group-Carrier = declared-in-safe-module Group.Carrier

st-Group-identity : st Group.identity
st-Group-identity = declared-in-safe-module Group.identity

st-Group-operation : st Group.operation
st-Group-operation = declared-in-safe-module Group.operation

st-Group-inverse : st Group.inverse
st-Group-inverse = declared-in-safe-module Group.inverse

st-Group-power : st Group.power
st-Group-power = declared-in-safe-module Group.power

st-FiniteGroup : st FiniteGroup
st-FiniteGroup = declared-in-safe-module FiniteGroup

st-FiniteGroup-Carrier : st FiniteGroup.Carrier
st-FiniteGroup-Carrier = declared-in-safe-module FiniteGroup.Carrier

st-FiniteGroup-identity : st FiniteGroup.identity
st-FiniteGroup-identity = declared-in-safe-module FiniteGroup.identity

st-FiniteGroup-operation : st FiniteGroup.operation
st-FiniteGroup-operation = declared-in-safe-module FiniteGroup.operation

st-FiniteGroup-inverse : st FiniteGroup.inverse
st-FiniteGroup-inverse = declared-in-safe-module FiniteGroup.inverse

st-FiniteGroup-order : st FiniteGroup.order
st-FiniteGroup-order = declared-in-safe-module FiniteGroup.order

st-FiniteGroup-power : st FiniteGroup.power
st-FiniteGroup-power = declared-in-safe-module FiniteGroup.power


st-PeriodicGroup : st PeriodicGroup
st-PeriodicGroup = declared-in-safe-module PeriodicGroup

st-PeriodicGroup-Carrier : st PeriodicGroup.Carrier
st-PeriodicGroup-Carrier = declared-in-safe-module PeriodicGroup.Carrier

st-PeriodicGroup-identity : st PeriodicGroup.identity
st-PeriodicGroup-identity = declared-in-safe-module PeriodicGroup.identity

st-PeriodicGroup-operation : st PeriodicGroup.operation
st-PeriodicGroup-operation = declared-in-safe-module PeriodicGroup.operation

st-PeriodicGroup-inverse : st PeriodicGroup.inverse
st-PeriodicGroup-inverse = declared-in-safe-module PeriodicGroup.inverse

st-PeriodicGroup-order : st PeriodicGroup.order
st-PeriodicGroup-order = declared-in-safe-module PeriodicGroup.order

st-PeriodicGroup-power : st PeriodicGroup.power
st-PeriodicGroup-power = declared-in-safe-module PeriodicGroup.power
