import Kleis.Wire.Decoder
import Kleis.Util.Json

/-!
# The JSON decoder

JSON is the one common format that cannot be decoded from a prefix: a truncated
object is not a smaller object, it is nothing.  So this decoder asks for the
whole body and gives up at the bound, which is the right trade for the bodies
that are actually JSON — an API call, not a packfile.
-/

namespace Kleis
namespace Wire

open LeanBiscuit (Bytes)

/-- Decode a complete JSON body.  An incomplete one is `need`; a complete one
that does not parse is `opaque`, not an error, because a body the origin would
have rejected is the origin's business and the policy layer's answer to a body
it cannot see into is already "no". -/
def jsonDecoder : PureDecoder where
  name := "json"
  media := #["application/json", "text/json", "application/vnd.api+json",
             "application/scim+json"]
  step := fun buf complete =>
    if !complete then .need (buf.size + 1)
    else match Json.parse (Bytes.toStringLossy buf) with
      | .ok j => .done j.toValue buf.size
      | .error _ => .opaque

end Wire
end Kleis
