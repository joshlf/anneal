import Trusted.Rustc.V2026_06_01.Layout

namespace Trusted.Layout

/-!
Default dialect alias re-exporting `Trusted.Rustc.V2026_06_01.Layout`.
-/

export Trusted.Rustc.V2026_06_01.Layout (
  Size Align isPowerOfTwoAux WrappingRange PrimitiveKind ScalarLayout
  FieldsShape VariantsShape BackendRepr TypeLayout AbiPassMode ArgAbi
  CallConv FnAbi LayoutTable
)

namespace Align
export Trusted.Rustc.V2026_06_01.Layout.Align (isPowerOfTwoBytes)
end Align

namespace Size
export Trusted.Rustc.V2026_06_01.Layout.Size (isMultipleOfAlign)
end Size

namespace TypeLayout
export Trusted.Rustc.V2026_06_01.Layout.TypeLayout (isWellFormed)
end TypeLayout

namespace LayoutTable
export Trusted.Rustc.V2026_06_01.Layout.LayoutTable (lookup)
end LayoutTable

end Trusted.Layout
