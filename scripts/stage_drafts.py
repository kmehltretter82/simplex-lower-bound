#!/usr/bin/env python3
"""Validate an offline packet or stage editable Prove2Me proposal drafts.

The default mode performs no network requests and reads no credentials.
There is deliberately no confirmation, submission, publication or launch code.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
from urllib.error import HTTPError, URLError
from urllib.parse import urlencode, urlsplit
from urllib.request import HTTPRedirectHandler, Request, build_opener

BASE = "https://prove2.me/api/v1"
PIN = "0df444a360eaa60ab8c11dca51a86af692955474"
SKILL_VERSION = "0.13.6"
ROOT = Path(__file__).resolve().parent.parent


class PacketError(Exception):
    pass


def digest(value):
    return hashlib.sha256(json.dumps(value, ensure_ascii=False, sort_keys=True).encode()).hexdigest()


def atomic_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")
    os.replace(temporary, path)


def validate(packet):
    proposal = packet.get("proposal", {})
    if proposal.get("mission_type") != "ResearchPaper":
        raise PacketError("proposal.mission_type must be ResearchPaper")
    if not proposal.get("name") or len(proposal["name"]) > 200:
        raise PacketError("proposal.name must contain 1–200 characters")
    if proposal.get("env") != PIN:
        raise PacketError("proposal.env must match the checked-in supported environment")
    if proposal.get("visibility", "public") not in {"public", "private"}:
        raise PacketError("invalid eventual mission visibility")
    if not proposal.get("description"):
        raise PacketError("proposal.description is required")
    items = packet.get("items", [])
    if not items:
        raise PacketError("packet has no draft items")
    keys = set()
    names = set()
    for item in items:
        key = item.get("key")
        if not key or key in keys:
            raise PacketError("every item needs a unique nonempty local key")
        keys.add(key)
        kind = item.get("kind")
        if kind == "definition":
            required = ["definition_name", "definition_title", "definition", "source"]
            name = item.get("definition_name", "")
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
                raise PacketError(f"invalid definition identifier for {key}")
            # Declaration-level placeholders are forbidden in definition modules.
            source = re.sub(r"/\-.*?\-/|--[^\n]*", "", item.get("definition", ""), flags=re.S)
            if re.search(r"\b(sorry|axiom|unsafe)\b", source):
                raise PacketError(f"definition {key} contains a forbidden placeholder or declaration")
        elif kind == "theorem":
            required = ["theorem_name", "theorem_title", "formal_statement", "preamble",
                        "natural_language_statement", "source"]
            name = item.get("theorem_name", "")
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", name):
                raise PacketError(f"invalid theorem identifier for {key}")
            statement = item.get("formal_statement", "")
            if ":= by sorry" not in statement:
                raise PacketError(f"theorem {key} must be an open target ending in := by sorry")
            if re.search(r"(?m)^\s*(?:noncomputable\s+)?(?:def|structure|inductive|axiom)\s", item.get("preamble", "")):
                raise PacketError(f"theorem {key} preamble contains a custom definition")
        elif kind == "reference":
            required = ["theorem_id"]
            name = "reference:" + item.get("theorem_id", "")
        else:
            raise PacketError(f"unsupported item kind: {kind}")
        if any(field not in item or not isinstance(item[field], str) or not item[field].strip()
               for field in required):
            raise PacketError(f"item {key} is missing a required field")
        if name in names:
            raise PacketError(f"duplicate item name: {name}")
        names.add(name)
        if kind != "reference" and (not item.get("readback") or not item.get("readback_model")):
            raise PacketError(f"item {key} needs an independent readback and readback_model")
    main_key = packet.get("main_key")
    by_key = {item["key"]: item for item in items}
    if main_key not in by_key or by_key[main_key]["kind"] not in {"theorem", "reference"}:
        raise PacketError("main_key must identify a goal theorem or reference")
    milestone_keys = set()
    for milestone in packet.get("milestones", []):
        key = milestone.get("key")
        if key not in by_key or key == main_key or by_key[key]["kind"] == "definition":
            raise PacketError("a milestone must identify a supporting theorem, not a definition or goal")
        if key in milestone_keys:
            raise PacketError("duplicate milestone item")
        milestone_keys.add(key)
        if not milestone.get("milestone_title") or not milestone.get("milestone_description"):
            raise PacketError(f"milestone {key} needs a title and description")
    return by_key


class NoRedirect(HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        raise PacketError("API redirect refused; credentials remain restricted to prove2.me/api/v1")


class API:
    def __init__(self, credentials, transport="urllib"):
        self.opener = build_opener(NoRedirect())
        self.transport = transport
        self.token = ""
        data = json.loads(credentials.read_text())
        token = data.get("access_token", "")
        expires = 0
        try:
            payload = token.split(".")[1]
            expires = json.loads(base64.urlsafe_b64decode(payload + "=" * (-len(payload) % 4)))["exp"]
        except (IndexError, ValueError, KeyError):
            pass
        if token and expires > time.time() + 120:
            self.token = token
        else:
            api_key = data.get("api_key")
            if not api_key:
                raise PacketError("saved access token expired; no saved API key is available")
            refreshed = self.request("POST", "/agent/refresh", {"api_key": api_key}, authenticate=False)
            if refreshed.get("version") != SKILL_VERSION:
                raise PacketError("platform version differs from the read captain schema; refresh the skill before staging")
            self.token = refreshed["access_token"]

    def request(self, method, path, body=None, authenticate=True):
        if not path.startswith("/") or ".." in path or "#" in path:
            raise PacketError("invalid API path")
        allowed = (
            method == "GET" and re.fullmatch(r"/(?:environments|fields|theorems|definitions|mission-proposals)(?:/[^/?]+)?(?:/milestones)?(?:\?.*)?", path)
        ) or (
            method in {"POST", "PATCH"} and re.fullmatch(
                r"/mission-proposals(?:/[A-Za-z0-9-]+)?(?:/(?:items|milestones)(?:/[A-Za-z0-9-]+)?)?", path)
        ) or (method == "POST" and path == "/agent/refresh" and not authenticate)
        if not allowed:
            raise PacketError("endpoint is outside the editable-draft allowlist")
        url = BASE + path
        parsed = urlsplit(url)
        if parsed.scheme != "https" or parsed.netloc != "prove2.me" or not parsed.path.startswith("/api/v1/"):
            raise PacketError("credentials may only be sent to the exact Prove2Me API")
        headers = {"Accept": "application/json", "User-Agent": "FriedmannMissionDrafts/1"}
        if authenticate:
            headers["Authorization"] = "Bearer " + self.token
        encoded = None
        if body is not None:
            encoded = json.dumps(body, ensure_ascii=False).encode()
            headers["Content-Type"] = "application/json"
        if self.transport in {"curl", "manual-curl"}:
            # Credentials stay in mode-0600 temporary files, never argv or
            # stdout. Redirects and retries remain disabled for all requests.
            with tempfile.TemporaryDirectory(prefix="p2m-credentials-") as directory:
                temporary = Path(directory)
                response_path = temporary / "response.json"
                config_path = temporary / "request.curl"
                lines = ["url = " + json.dumps(url), "request = " + json.dumps(method),
                         "output = " + json.dumps(str(response_path))]
                lines.extend("header = " + json.dumps(k + ": " + v) for k, v in headers.items())
                if encoded is not None:
                    body_path = temporary / "body.json"
                    body_path.write_bytes(encoded)
                    body_path.chmod(0o600)
                    lines.append("data-binary = " + json.dumps("@" + str(body_path)))
                config_path.write_text("\n".join(lines) + "\n")
                config_path.chmod(0o600)
                if self.transport == "manual-curl":
                    # The caller executes this same constrained curl request
                    # through its approved network tool, then supplies status.
                    print("CURL_REQUEST " + json.dumps({"method": method, "path": path,
                        "config": str(config_path)}), flush=True)
                    status = sys.stdin.readline().strip()
                    code = 0 if re.fullmatch(r"2\d\d", status) else 1
                else:
                    result = subprocess.run(["curl", "-fL", "--silent", "--show-error",
                        "--max-redirs", "0", "--proto", "=https", "--max-time", "45",
                        "--write-out", "%{http_code}", "--config", str(config_path)],
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                    status = result.stdout.decode(errors="replace").strip()
                    code = result.returncode
                if code or not re.fullmatch(r"2\d\d", status):
                    raise PacketError(f"API curl failure (exit {code}, HTTP {status}) for {method} {path.split('?')[0]}; no automatic retry")
                return json.loads(response_path.read_text())
        request = Request(url, data=encoded, headers=headers, method=method)
        try:
            with self.opener.open(request, timeout=45) as response:
                return json.load(response)
        except HTTPError as exc:
            # Do not echo request or response bodies: auth endpoints can carry credentials.
            raise PacketError(f"API HTTP {exc.code} for {method} {path.split('?')[0]}") from None
        except URLError as exc:
            raise PacketError(f"API connection failed ({type(exc.reason).__name__}); no automatic retry") from None


def api_body(item):
    if item["kind"] == "reference":
        fields = {"kind", "theorem_id"}
    elif item["kind"] == "definition":
        fields = {"kind", "definition_name", "definition_title", "definition", "natural_language_statement",
                  "source", "tags", "readback", "readback_model"}
    else:
        fields = {"kind", "theorem_name", "theorem_title", "formal_statement", "preamble",
                  "natural_language_statement", "source", "tags", "readback", "readback_model"}
    return {key: value for key, value in item.items() if key in fields}


def item_name(item):
    return item.get("theorem_name") or item.get("definition_name") or item.get("theorem_id")


def same_item(remote, local):
    body = api_body(local)
    for key, value in body.items():
        if key == "kind":
            continue
        remote_value = remote.get(key)
        if key == "definition_name":
            remote_value = remote.get(key, remote.get("theorem_name"))
        elif key == "definition_title":
            remote_value = remote.get(key, remote.get("theorem_title"))
        if remote_value != value:
            return False
    return True


def list_values(result, key):
    return result if isinstance(result, list) else result.get(key, result.get("items", []))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("packet", type=Path)
    parser.add_argument("--write", action="store_true", help="stage editable drafts; never launch or publish")
    parser.add_argument("--credentials", type=Path, default=Path.home() / "prove2me_workspace/credentials.json")
    parser.add_argument("--state", type=Path)
    parser.add_argument("--field-id", action="append", default=[])
    parser.add_argument("--reconcile", action="store_true", help="read server state after an ambiguous write; never retry it blindly")
    parser.add_argument("--transport", choices=["urllib", "curl", "manual-curl"], default="urllib")
    args = parser.parse_args()
    packet = json.loads(args.packet.read_text())
    by_key = validate(packet)
    if args.field_id:
        packet["proposal"]["field_ids"] = args.field_id
    state_path = args.state or args.packet.with_name(args.packet.stem + ".state.json")
    print(f"Validated {len(packet['items'])} ordered items and {len(packet.get('milestones', []))} milestones")
    print(f"Goal: {item_name(by_key[packet['main_key']])}")
    print(f"Packet SHA256: {digest(packet)}")
    if not args.write and not args.reconcile:
        print("Dry run only: no network requests, no credentials read, no server changes")
        return
    if not packet["proposal"].get("field_ids"):
        raise PacketError("resolve at least one existing field UUID, then pass --field-id; no fields are created by this helper")
    api = API(args.credentials, transport=args.transport)
    environments = list_values(api.request("GET", "/environments"), "environments")
    if not any(env.get("mathlib_rev") == PIN for env in environments):
        raise PacketError("the locally checked environment is not offered by the live platform")
    state = json.loads(state_path.read_text()) if state_path.exists() else {"items": {}, "milestones": {}, "proposal_id": None}
    if state.get("pending"):
        pending = state["pending"]
        if not args.reconcile:
            raise PacketError("previous write is ambiguous: run --reconcile first; it will not repeat the POST")
        if not state.get("proposal_id"):
            matches = []
            offset = 0
            while True:
                response = api.request("GET", "/mission-proposals?" + urlencode({"limit": 100, "offset": offset}))
                proposals = list_values(response, "proposals")
                matches.extend(p for p in proposals if p.get("name") == packet["proposal"]["name"])
                if len(proposals) < 100:
                    break
                offset += 100
            if len(matches) != 1:
                raise PacketError("could not identify exactly one proposal after ambiguous create; inspect My Missions before changing state")
            state["proposal_id"] = matches[0]["id"]
        proposal = api.request("GET", "/mission-proposals/" + state["proposal_id"])
        if pending.get("key"):
            local = by_key[pending["key"]]
            matches = [i for i in proposal.get("items", []) if item_name(i) == item_name(local)]
            if len(matches) != 1 or not same_item(matches[0], local):
                raise PacketError("ambiguous item is not present with exactly the intended body; inspect proposal before changing local state")
            state["items"][pending["key"]] = {"id": matches[0]["id"], "hash": digest(api_body(local))}
        elif pending["path"].endswith("/milestones"):
            raise PacketError("inspect proposal milestone state manually; no blind milestone retry is performed")
        else:
            body = pending.get("body", {})
            if any(proposal.get(k) != v for k, v in body.items() if k not in {"field_ids"}):
                raise PacketError("ambiguous metadata write does not match server state; inspect before changing local state")
        state.pop("pending")
        atomic_json(state_path, state)
        print("Previous write reconciled from server reads; rerun --write to continue")
        return
    if args.reconcile:
        print("No ambiguous write to reconcile")
        return
    # Shared models are published once. Subsequent paper drafts reference an
    # exactly identical published declaration instead of attempting to publish
    # the same globally named module again. Different code still stops staging.
    library_matches = []
    for index, item in enumerate(packet["items"]):
        if item["kind"] == "reference":
            continue
        endpoint = "/definitions" if item["kind"] == "definition" else "/theorems"
        name_field = "definition_name" if item["kind"] == "definition" else "theorem_name"
        results = api.request("GET", endpoint + "?" + urlencode(
            {name_field: item_name(item), "view": "compact", "env": PIN, "limit": 20}))
        values = list_values(results, "definitions" if endpoint == "/definitions" else "theorems")
        if values:
            same = [v for v in values if v.get(name_field) == item_name(item) and
                ((item["kind"] == "definition" and v.get("definition", "").strip() == item["definition"].strip()) or
                 (item["kind"] == "theorem" and
                  v.get("formal_statement", "").strip() == item["formal_statement"].strip() and
                  v.get("preamble", "").strip() == item["preamble"].strip()))]
            if len(same) == 1 and item["key"] not in state["items"]:
                existing_id = same[0].get("definition_id") or same[0].get("theorem_id")
                if not existing_id:
                    raise PacketError("identical library result has no canonical ID")
                reference = {"key": item["key"], "kind": "reference", "theorem_id": existing_id}
                packet["items"][index] = reference
                by_key[item["key"]] = reference
                print("Reusing identical published declaration: " + item_name(item))
            else:
                library_matches.append(item_name(item))
    if library_matches:
        raise PacketError("existing library matches require review before duplicate drafting: " + ", ".join(library_matches))

    def write(method, path, body, key=None):
        state["pending"] = {"method": method, "path": path, "body": body, "body_sha256": digest(body), "key": key}
        atomic_json(state_path, state)
        result = api.request(method, path, body)
        state.pop("pending")
        return result

    proposal_fields = {"name", "description", "mission_type", "field_ids", "env", "visibility"}
    metadata = {k: v for k, v in packet["proposal"].items() if k in proposal_fields}
    if not state["proposal_id"]:
        result = write("POST", "/mission-proposals", metadata)
        state["proposal_id"] = result["id"]
        atomic_json(state_path, state)
    proposal_id = state["proposal_id"]
    proposal = api.request("GET", "/mission-proposals/" + proposal_id)
    if proposal.get("status") != "Draft":
        raise PacketError("helper only edits Draft proposals; current state is " + str(proposal.get("status")))
    write("PATCH", "/mission-proposals/" + proposal_id, metadata)
    atomic_json(state_path, state)
    for item in packet["items"]:
        key = item["key"]
        body = api_body(item)
        previous = state["items"].get(key)
        if previous and previous["hash"] == digest(body):
            continue
        if previous:
            path = f"/mission-proposals/{proposal_id}/items/{previous['id']}"
            result = write("PATCH", path, {k: v for k, v in body.items() if k != "kind"}, key)
        else:
            result = write("POST", f"/mission-proposals/{proposal_id}/items", body, key)
        state["items"][key] = {"id": result["id"], "hash": digest(body)}
        atomic_json(state_path, state)
    order = [state["items"][item["key"]]["id"] for item in packet["items"]]
    write("PATCH", "/mission-proposals/" + proposal_id,
          {"main_item_id": state["items"][packet["main_key"]]["id"], "item_order": order})
    atomic_json(state_path, state)
    for milestone in packet.get("milestones", []):
        key = milestone["key"]
        body = {"item_id": state["items"][key]["id"], "milestone_title": milestone["milestone_title"],
                "milestone_description": milestone["milestone_description"]}
        if state["milestones"].get(key) == digest(body):
            continue
        write("POST", f"/mission-proposals/{proposal_id}/milestones", body)
        state["milestones"][key] = digest(body)
        atomic_json(state_path, state)
    final = api.request("GET", "/mission-proposals/" + proposal_id)
    if final.get("status") != "Draft":
        raise PacketError("server did not return the expected unpublished Draft state")
    print("Draft staged, status Draft: " + proposal_id)
    print("Review via https://prove2.me/my-missions; this helper cannot confirm or submit it")


if __name__ == "__main__":
    try:
        main()
    except (PacketError, OSError, ValueError, KeyError) as exc:
        print("Stopped: " + str(exc), file=sys.stderr)
        sys.exit(1)
