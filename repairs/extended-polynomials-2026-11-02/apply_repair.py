#!/usr/bin/env python3
"""Safe existing-proposal draft replacement driver for Extended Polynomials (059a0f02-b778-44fd-9e95-ec7cbdba9cbc).

Follows upload-plan.txt:
- Exact-name collision preflight with include_deprecated=true.
- ADD -> VERIFY -> RELINK -> REMOVE -> ORDER -> FINAL VERIFY.
- Never confirms, submits, publishes, or launches.
- Credentials remain in mode-0600 temporary curl configs; never echoed to argv/stdout/files.
"""
from __future__ import annotations

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
from urllib.parse import urlencode, urlsplit

HERE = Path(__file__).resolve().parent
BASE = "https://prove2.me/api/v1"
PROPOSAL_ID = "059a0f02-b778-44fd-9e95-ec7cbdba9cbc"
PIN = "0df444a360eaa60ab8c11dca51a86af692955474"
SKILL_VERSION = "0.13.6"

OLD_ITEM_IDS = [
    "d07ad5a1-b497-4253-be46-eb89793c50a6",
    "6e273f62-64c5-4318-a05a-8a39e52eee4b",
    "642dc3db-853f-4e6d-bd9b-14deebeae480",
    "2d2c21d1-df7a-4961-a241-c2df62884098",
    "8f16f779-9541-4d5f-806c-a29a44f333c7",
]
OLD_MILESTONE_ITEM_IDS = [
    "6e273f62-64c5-4318-a05a-8a39e52eee4b",
    "642dc3db-853f-4e6d-bd9b-14deebeae480",
    "2d2c21d1-df7a-4961-a241-c2df62884098",
]


class RepairError(Exception):
    pass


def digest(value) -> str:
    return hashlib.sha256(json.dumps(value, ensure_ascii=False, sort_keys=True).encode()).hexdigest()


def atomic_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")
    os.replace(tmp, path)


class CurlAPI:
    def __init__(self, credentials: Path):
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
                raise RepairError("saved access token expired and no api_key present")
            refreshed = self.request("POST", "/agent/refresh", {"api_key": api_key}, authenticate=False)
            if refreshed.get("version") != SKILL_VERSION:
                raise RepairError(f"platform version {refreshed.get('version')} != {SKILL_VERSION}")
            self.token = refreshed["access_token"]

    def request(self, method: str, path: str, body=None, authenticate: bool = True):
        if not path.startswith("/") or ".." in path or "#" in path:
            raise RepairError(f"invalid API path: {path}")
        allowed = (
            (method == "GET" and re.fullmatch(
                r"/(?:health|environments|definitions|theorems|mission-proposals)(?:/[^/?]+)?(?:/milestones)?(?:\?.*)?",
                path))
            or (method in {"POST", "PATCH", "DELETE"} and re.fullmatch(
                rf"/mission-proposals/{PROPOSAL_ID}(?:/(?:items|milestones)(?:/[A-Za-z0-9-]+)?)?",
                path))
            or (method == "POST" and path == "/agent/refresh" and not authenticate)
        )
        if not allowed:
            raise RepairError(f"disallowed endpoint: {method} {path}")
        url = BASE + path
        parsed = urlsplit(url)
        if parsed.scheme != "https" or parsed.netloc != "prove2.me" or not parsed.path.startswith("/api/v1/"):
            raise RepairError("credentials restricted to https://prove2.me/api/v1/")
        headers = {"Accept": "application/json", "User-Agent": "SchwichtenbergRepair/1"}
        if authenticate:
            headers["Authorization"] = "Bearer " + self.token
        encoded = None
        if body is not None:
            encoded = json.dumps(body, ensure_ascii=False).encode()
            headers["Content-Type"] = "application/json"
        with tempfile.TemporaryDirectory(prefix="p2m-credentials-") as directory:
            tmp = Path(directory)
            response_path = tmp / "response.json"
            config_path = tmp / "request.curl"
            lines = [
                "url = " + json.dumps(url),
                "request = " + json.dumps(method),
                "output = " + json.dumps(str(response_path)),
            ]
            lines.extend("header = " + json.dumps(f"{k}: {v}") for k, v in headers.items())
            if encoded is not None:
                body_path = tmp / "body.json"
                body_path.write_bytes(encoded)
                body_path.chmod(0o600)
                lines.append("data-binary = " + json.dumps("@" + str(body_path)))
            config_path.write_text("\n".join(lines) + "\n")
            config_path.chmod(0o600)
            result = subprocess.run(
                [
                    "curl", "-fL", "--silent", "--show-error",
                    "--max-redirs", "0", "--proto", "=https", "--max-time", "45",
                    "--write-out", "%{http_code}", "--config", str(config_path),
                ],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            status = result.stdout.decode(errors="replace").strip()
            if result.returncode or not re.fullmatch(r"2\d\d", status):
                raise RepairError(
                    f"API curl failure (exit {result.returncode}, HTTP {status}) for {method} {path.split('?')[0]}"
                )
            if status == "204" or not response_path.exists() or response_path.stat().st_size == 0:
                return None
            return json.loads(response_path.read_text())


def api_body(item: dict) -> dict:
    if item["kind"] == "definition":
        fields = {
            "kind", "definition_name", "definition_title", "definition",
            "natural_language_statement", "source", "tags", "readback", "readback_model",
        }
    else:
        fields = {
            "kind", "theorem_name", "theorem_title", "formal_statement", "preamble",
            "natural_language_statement", "source", "tags", "readback", "readback_model",
        }
    return {k: v for k, v in item.items() if k in fields}


def item_name(item: dict) -> str:
    return item.get("definition_name") or item.get("theorem_name") or item.get("theorem_id")


def verify_remote_item(remote: dict, local: dict) -> None:
    expected = api_body(local)
    for k, v in expected.items():
        if k == "kind":
            if remote.get("kind") != v:
                raise RepairError(f"kind mismatch on {item_name(local)}: {remote.get('kind')} != {v}")
            continue
        if k == "definition_name":
            rv = remote.get("definition_name") or remote.get("theorem_name")
        elif k == "definition_title":
            rv = remote.get("definition_title") or remote.get("theorem_title")
        elif k == "tags":
            rv = sorted(remote.get("tags", []))
            v = sorted(v)
        else:
            rv = remote.get(k)
        if rv != v:
            raise RepairError(f"field {k} mismatch on {item_name(local)}")


def main() -> None:
    packet_path = HERE / "packet-v2.json"
    state_path = HERE / "repair-state.json"
    packet = json.loads(packet_path.read_text())
    state = json.loads(state_path.read_text()) if state_path.exists() else {
        "proposal_id": PROPOSAL_ID,
        "new_items": {},
        "new_milestones": {},
        "removed_old_milestones": [],
        "removed_old_items": [],
    }
    if state.get("pending"):
        raise RepairError(f"Ambiguous pending write in {state_path}: inspect before continuing")

    api = CurlAPI(Path.home() / "prove2me_workspace/credentials.json")

    def write(method: str, path: str, body=None, step: str = ""):
        state["pending"] = {"step": step, "method": method, "path": path, "body_sha256": digest(body)}
        atomic_json(state_path, state)
        res = api.request(method, path, body)
        state.pop("pending", None)
        atomic_json(state_path, state)
        return res

    # 1. Read-only preflight: health, environments, proposal, milestones, exact-name searches
    health = api.request("GET", "/health", authenticate=False)
    if health.get("version") != SKILL_VERSION:
        raise RepairError(f"Unexpected API version: {health.get('version')}")
    envs = api.request("GET", "/environments").get("environments", [])
    if not any(e.get("mathlib_rev") == PIN for e in envs):
        raise RepairError("Pinned environment not offered")

    prop = api.request("GET", f"/mission-proposals/{PROPOSAL_ID}")
    if prop.get("status") != "Draft":
        raise RepairError(f"Proposal status is {prop.get('status')}, expected Draft")
    if prop.get("env") != PIN:
        raise RepairError(f"Proposal env is {prop.get('env')}, expected {PIN}")

    exact_checks = {}
    for item in packet["items"]:
        name = item_name(item)
        if item["kind"] == "definition":
            q = urlencode({"definition_name": name, "include_deprecated": "true", "env": PIN, "limit": 20})
            res = api.request("GET", f"/definitions?{q}")
            hits = [d for d in res.get("definitions", []) if d.get("definition_name") == name]
        else:
            q = urlencode({"theorem_name": name, "include_deprecated": "true", "env": PIN, "limit": 20})
            res = api.request("GET", f"/theorems?{q}")
            hits = [t for t in res.get("theorems", []) if t.get("theorem_name") == name]
        if hits:
            raise RepairError(f"Exact name collision in published/deprecated catalog for {name}")
        exact_checks[name] = 0
    print("Preflight passed; exact-name collisions:", exact_checks, flush=True)

    # Step A: POST the 5 new draft items in dependency order
    for item in packet["items"]:
        key = item["key"]
        body = api_body(item)
        body_hash = digest(body)
        existing = state["new_items"].get(key)
        if existing and existing.get("hash") == body_hash:
            continue
        res = write("POST", f"/mission-proposals/{PROPOSAL_ID}/items", body, step=f"post_item:{key}")
        state["new_items"][key] = {"id": res["id"], "name": item_name(item), "hash": body_hash}
        atomic_json(state_path, state)
        print(f"Staged draft item {key} -> {res['id']} ({item_name(item)})", flush=True)

    # Step B: GET proposal and verify all 5 new draft items byte-for-byte
    prop_check = api.request("GET", f"/mission-proposals/{PROPOSAL_ID}")
    remote_by_id = {it["id"]: it for it in prop_check.get("items", [])}
    for item in packet["items"]:
        key = item["key"]
        iid = state["new_items"][key]["id"]
        if iid not in remote_by_id:
            raise RepairError(f"Newly staged item {key} ({iid}) missing from proposal readback")
        verify_remote_item(remote_by_id[iid], item)
    print("Verified all 5 new draft items byte-for-byte on proposal.", flush=True)

    # Step C: POST milestones for the 3 new supporting theorem items
    for ms in packet["milestones"]:
        key = ms["key"]
        iid = state["new_items"][key]["id"]
        ms_body = {
            "item_id": iid,
            "milestone_title": ms["milestone_title"],
            "milestone_description": ms["milestone_description"],
        }
        ms_hash = digest(ms_body)
        if state["new_milestones"].get(key) == ms_hash:
            continue
        write("POST", f"/mission-proposals/{PROPOSAL_ID}/milestones", ms_body, step=f"post_milestone:{key}")
        state["new_milestones"][key] = ms_hash
        atomic_json(state_path, state)
        print(f"Linked new milestone {key} -> {iid}", flush=True)

    # Step D: Switch main_item_id directly to the new goal item ID
    new_goal_id = state["new_items"][packet["main_key"]]["id"]
    write(
        "PATCH",
        f"/mission-proposals/{PROPOSAL_ID}",
        {"main_item_id": new_goal_id},
        step="retarget_main_item_id",
    )
    print(f"Retargeted main_item_id -> {new_goal_id}", flush=True)

    # Step E: DELETE old milestone links and DELETE old reference items
    current_ms = api.request("GET", f"/mission-proposals/{PROPOSAL_ID}/milestones").get("milestones", [])
    current_ms_ids = {m["item_id"] for m in current_ms}
    for old_ms_id in OLD_MILESTONE_ITEM_IDS:
        if old_ms_id in current_ms_ids:
            write(
                "DELETE",
                f"/mission-proposals/{PROPOSAL_ID}/milestones/{old_ms_id}",
                step=f"delete_old_milestone:{old_ms_id}",
            )
            state["removed_old_milestones"].append(old_ms_id)
            atomic_json(state_path, state)
            print(f"Removed old milestone role {old_ms_id}", flush=True)

    current_prop = api.request("GET", f"/mission-proposals/{PROPOSAL_ID}")
    current_item_ids = {it["id"] for it in current_prop.get("items", [])}
    for old_iid in OLD_ITEM_IDS:
        if old_iid in current_item_ids:
            write(
                "DELETE",
                f"/mission-proposals/{PROPOSAL_ID}/items/{old_iid}",
                step=f"delete_old_item:{old_iid}",
            )
            state["removed_old_items"].append(old_iid)
            atomic_json(state_path, state)
            print(f"Removed old reference item {old_iid}", flush=True)

    # Step F: PATCH proposal description, main_item_id, and final item_order
    final_order = [state["new_items"][it["key"]]["id"] for it in packet["items"]]
    write(
        "PATCH",
        f"/mission-proposals/{PROPOSAL_ID}",
        {
            "description": packet["proposal"]["description"],
            "main_item_id": new_goal_id,
            "item_order": final_order,
        },
        step="patch_final_metadata_and_order",
    )
    print("Patched final description, main_item_id, and item_order.", flush=True)

    # Step G: Final readback verification and receipt
    final_prop = api.request("GET", f"/mission-proposals/{PROPOSAL_ID}")
    final_ms = api.request("GET", f"/mission-proposals/{PROPOSAL_ID}/milestones")
    atomic_json(HERE / "proposal-after-repair.json", final_prop)
    atomic_json(HERE / "milestones-after-repair.json", final_ms)

    if final_prop.get("status") != "Draft":
        raise RepairError(f"Final status is {final_prop.get('status')}, expected Draft")
    if final_prop.get("item_order") != final_order:
        raise RepairError("Final item_order mismatch")
    if final_prop.get("main_item_id") != new_goal_id:
        raise RepairError("Final main_item_id mismatch")
    if len(final_prop.get("items", [])) != 5:
        raise RepairError(f"Expected 5 items, found {len(final_prop.get('items', []))}")
    final_by_id = {it["id"]: it for it in final_prop["items"]}
    for item in packet["items"]:
        iid = state["new_items"][item["key"]]["id"]
        verify_remote_item(final_by_id[iid], item)
        if final_by_id[iid].get("kind") == "reference":
            raise RepairError(f"Item {iid} is unexpectedly a reference")

    ms_list = final_ms.get("milestones", [])
    if len(ms_list) != 3:
        raise RepairError(f"Expected 3 milestones, found {len(ms_list)}")
    expected_ms_ids = [state["new_items"][m["key"]]["id"] for m in packet["milestones"]]
    if [m["item_id"] for m in ms_list] != expected_ms_ids:
        raise RepairError("Final milestone order/IDs mismatch")

    receipt = {
        "proposal_id": PROPOSAL_ID,
        "status": final_prop["status"],
        "env": final_prop["env"],
        "main_item_id": final_prop["main_item_id"],
        "item_order": final_prop["item_order"],
        "old_to_new_items": {
            OLD_ITEM_IDS[i]: {
                "key": packet["items"][i]["key"],
                "new_item_id": state["new_items"][packet["items"][i]["key"]]["id"],
                "name": item_name(packet["items"][i]),
            }
            for i in range(5)
        },
        "packet_sha256": digest(packet),
        "proposal_after_sha256": digest(final_prop),
        "milestones_after_sha256": digest(final_ms),
    }
    atomic_json(HERE / "repair-receipt.json", receipt)
    print("REPAIR_COMPLETE", json.dumps(receipt, indent=2), flush=True)


if __name__ == "__main__":
    main()
