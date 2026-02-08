module Lsp_types = Linol_lsp.Types

let hover_at
    (result : Analysis.analysis_result)
    (idx : Index.index)
    (pos : Lsp_types.Position.t)
  : Lsp_types.Hover.t option =
  match Index.find_at_position idx pos with
  | None -> None
  | Some entry ->
    let type_str =
      match result.type_env, result.final_subst with
      | Some env, Some subst ->
        (match List.assoc_opt entry.name env with
         | Some sc ->
           let (Types.Forall (_, t)) = sc in
           let resolved = Types.apply_subst subst t in
           Some (Types.string_of_scheme (Types.Forall ([], resolved)))
         | None -> None)
      | _ -> None
    in
    let content =
      match type_str with
      | Some ty -> Printf.sprintf "**%s** : `%s`" entry.name ty
      | None -> Printf.sprintf "**%s**" entry.name
    in
    let hover =
      Lsp_types.Hover.create
        ~contents:(`MarkupContent
          (Lsp_types.MarkupContent.create
             ~kind:Lsp_types.MarkupKind.Markdown
             ~value:content))
        ~range:(Span_utils.sourcespan_to_range entry.def_span)
        ()
    in
    Some hover
