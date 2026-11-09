import LeanMiriSpec
open Miri.Memory
#eval InitMask.noBytesInit (InitMask.new (Miri.ABI.Size.ofBytes 4) false)
