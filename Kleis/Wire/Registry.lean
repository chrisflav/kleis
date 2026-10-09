import Kleis.Wire.Json
import Kleis.Wire.Form
import Kleis.Wire.Git
import Kleis.Wire.GraphQL

/-!
# The decoder registry

The one place that knows which formats exist.  A manifest names a decoder by
its registry name, or binds a media type to one; nothing else in the system has
a list of formats in it.

This is the code-side seam the design admits to: a service speaking a format
nobody has written a decoder for needs Lean, once, for the *format* — not for
the service.
-/

namespace Kleis
namespace Wire

/-- Every shipped decoder. -/
def shipped : List PureDecoder :=
  [jsonDecoder, graphqlDecoder, formDecoder, multipartDecoder, gitReceivePackDecoder,
   gitUploadPackDecoder, opaqueDecoder]

/-- Look up a decoder by the name a manifest uses. -/
def byName? (name : String) : Option PureDecoder :=
  shipped.find? fun d => d.name == name

/-- The decoder that claims a media type by default.

The type is matched on its bare form: parameters like `; charset=utf-8` are
part of the field but not of the type, and a manifest that had to spell them
out would break the first time a client added one. -/
def byMedia? (contentType : String) : Option PureDecoder :=
  let bare := Str.toLowerAscii (Str.trim ((contentType.splitOn ";").headD contentType))
  shipped.find? fun d => d.media.contains bare

end Wire
end Kleis
