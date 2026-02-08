module Lsp_types = Linol_lsp.Types

let goto_definition
    (idx : Index.index)
    (uri : Lsp_types.DocumentUri.t)
    (pos : Lsp_types.Position.t)
  : Lsp_types.Locations.t option =
  match Index.find_at_position idx pos with
  | None -> None
  | Some entry ->
    let loc =
      Lsp_types.Location.create
        ~uri
        ~range:(Span_utils.sourcespan_to_range entry.def_span)
    in
    Some (`Location [loc])
