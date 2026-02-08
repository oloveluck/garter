module Lsp_types = Linol_lsp.Types

type doc_data = {
  analysis : Analysis.analysis_result;
  index : Index.index option;
}

let analyze_and_store ~uri ~content : doc_data =
  let result = Analysis.analyze ~uri ~source:content in
  let index =
    match result.program with
    | Some prog -> Some (Index.build_index prog)
    | None -> None
  in
  { analysis = result; index }

class garter_server =
  object (self)
    inherit Linol_lwt.Jsonrpc2.server

    val store : (Lsp_types.DocumentUri.t, doc_data) Hashtbl.t =
      Hashtbl.create 16

    method spawn_query_handler f = Linol_lwt.spawn f

    (* Advertise capabilities *)
    method! config_hover = Some (`Bool true)
    method! config_definition = Some (`Bool true)

    method private _analyze_and_publish
        ~(notify_back : Linol_lwt.Jsonrpc2.notify_back)
        (uri : Lsp_types.DocumentUri.t)
        (content : string) =
      let uri_str = Lsp_types.DocumentUri.to_path uri in
      let data = analyze_and_store ~uri:uri_str ~content in
      Hashtbl.replace store uri data;
      notify_back#send_diagnostic data.analysis.diagnostics

    (* Document lifecycle *)
    method on_notif_doc_did_open
        ~(notify_back : Linol_lwt.Jsonrpc2.notify_back)
        (doc : Lsp_types.TextDocumentItem.t)
        ~(content : string) =
      self#_analyze_and_publish ~notify_back doc.uri content

    method on_notif_doc_did_change
        ~(notify_back : Linol_lwt.Jsonrpc2.notify_back)
        (doc : Lsp_types.VersionedTextDocumentIdentifier.t)
        (_changes : Lsp_types.TextDocumentContentChangeEvent.t list)
        ~(old_content : string)
        ~(new_content : string) =
      ignore old_content;
      self#_analyze_and_publish ~notify_back doc.uri new_content

    method on_notif_doc_did_close
        ~(notify_back : Linol_lwt.Jsonrpc2.notify_back)
        (doc : Lsp_types.TextDocumentIdentifier.t) =
      Hashtbl.remove store doc.uri;
      notify_back#send_diagnostic []

    (* Hover handler *)
    method! on_req_hover
        ~notify_back:(_notify_back : Linol_lwt.Jsonrpc2.notify_back)
        ~id:_ ~uri
        ~pos
        ~workDoneToken:_
        (_doc : Linol_lwt.doc_state) =
      let result =
        match Hashtbl.find_opt store uri with
        | None -> None
        | Some data ->
          (match data.index with
           | None -> None
           | Some idx -> Hover.hover_at data.analysis idx pos)
      in
      Lwt.return result

    (* Go-to-definition handler *)
    method! on_req_definition
        ~notify_back:(_notify_back : Linol_lwt.Jsonrpc2.notify_back)
        ~id:_ ~uri
        ~pos
        ~workDoneToken:_ ~partialResultToken:_
        (_doc : Linol_lwt.doc_state) =
      let result =
        match Hashtbl.find_opt store uri with
        | None -> None
        | Some data ->
          (match data.index with
           | None -> None
           | Some idx -> Navigation.goto_definition idx uri pos)
      in
      Lwt.return result
  end
