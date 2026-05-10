# rfc8738-verified: remaining work

Done:
- `theories/RFC8738_Prelude.v` — numeric types, digit/hex predicates, string helpers, decidable equality.
- `theories/RFC8738_IPv4.v` — IPv4 ADT, RFC 1123 §2.1 dotted-decimal printer/parser, leading-zero rejection, **proven full round-trip** `parse_print_ipv4`, byte-encoding.
- `theories/RFC8738_IPv6.v` — IPv6 ADT (8×16-bit groups), RFC 5952 canonical printer (lowercase hex, leading-zero suppression, longest-zero-run compression with leftmost tie-break, single-zero non-compression rule), parser handling `::` and uppercase/lowercase hex, `is_ipv4_mapped` predicate, byte-encoding, **representative RFC 5952 examples verified by `vm_compute`** (unspecified, loopback, documentation prefix, no-compression, leftmost-run tie-break, single-zero non-compression).
- `theories/RFC8738_Identifier.v` — `ip_address` sum type, ACME identifier record per RFC 8555 §7.1.4, type "ip" enforcement, **proven** `parse_ip_identifier_*` correspondence theorems for every error/ok case, **proven** RFC 8738 §3 IPv4-mapped IPv6 rejection (`ipv4_mapped_v6_rejected`), **proven** end-to-end IPv4 round-trip through the discriminating parser (`print_parse_ipv4_round_trip`).

Remaining:

1. **`theories/RFC8738_SAN.v`** — RFC 5280 SAN integration.
   - `Inductive general_name := GN_dNSName (s:string) | GN_iPAddress (bs:list byte) | GN_other`.
   - `general_name_for_ip : ip_address -> general_name` producing `GN_iPAddress` with the canonical 4-byte (v4) or 16-byte (v6) octet string.
   - `san_matches_ip : list general_name -> ip_address -> bool` walking the SAN list.
   - **Theorem** `san_matches_for_ip` : the SAN built by `general_name_for_ip` matches the originating IP.
   - **Theorem** `san_byte_length_v4` : encoding always yields exactly 4 octets for v4.
   - **Theorem** `san_byte_length_v6` : encoding always yields exactly 16 octets for v6.
   - **Theorem** `san_dns_name_does_not_match_ip` : RFC 8738 §4.2 explicitly mandates `iPAddress`, not `dNSName`; this proves the negative case.

2. **`theories/RFC8738_ACME8737.v`** — RFC 8737 acmeIdentifier extension stub.
   - `Record acmeIdentifier := { ai_critical : bool; ai_value : list byte }` (the SHA-256 of the key authorization).
   - `key_authorization : token -> jwk_thumbprint -> string`.
   - `mk_acme_identifier_extension : token -> jwk_thumbprint -> acmeIdentifier`.
   - **Theorem** `acme_identifier_critical` : `ai_critical = true` is mandatory per RFC 8737 §3.

3. **`theories/RFC8738_Challenge.v`** — Challenge layer.
   - `Inductive acme_challenge_type := HTTP_01 | TLS_ALPN_01 | DNS_01`.
   - `Definition ip_supported_challenges : list acme_challenge_type := [HTTP_01; TLS_ALPN_01]`.
   - **Theorem** `dns01_not_supported_for_ip : ~ In DNS_01 ip_supported_challenges` (RFC 8738 §4.3).
   - **Theorem** `dns01_supported_for_ip_b : In_dec DNS_01 ip_supported_challenges = false`.
   - HTTP-01 URL builder: `build_http01_url : ip_address -> string -> string` constructing `http://<host>/.well-known/acme-challenge/<token>` with IPv6 brackets per RFC 8738 §4.1.
   - **Theorem** `http01_url_brackets_iff_ipv6` : the URL host is bracketed iff the IP is IPv6.
   - **Theorem** `http01_url_well_known_path` : the path is always `/.well-known/acme-challenge/<token>`.
   - TLS-ALPN-01 challenge cert validation: `tls_alpn_san_check : Certificate -> ip_address -> acmeIdentifier -> bool` enforcing iPAddress SAN per RFC 8738 §4.2 + RFC 8737 acmeIdentifier extension.
   - **Theorem** `tls_alpn_san_uses_ip_address_not_dns_name` : the cert MUST use `iPAddress`, not `dNSName`.

4. **`theories/RFC8738_Workflow.v`** — End-to-end pipeline.
   - `Definition verify_ip_identifier_workflow : acme_identifier -> challenge_response -> Certificate -> bool`.
   - **Theorem** `workflow_sound` : if the workflow accepts, then (a) the identifier was canonical, (b) it was not IPv4-mapped, (c) the challenge was HTTP-01 or TLS-ALPN-01 (not DNS-01), (d) the certificate's SAN matches the identifier's IP.
   - **Theorem** `workflow_rejects_dns01_for_ip` : negative case for DNS-01.
   - **Theorem** `workflow_rejects_ipv4_mapped` : negative case for `::ffff:a.b.c.d`.

5. **`theories/RFC8738_API.v`** — User-facing API + extraction.
   - Module `API` with: `parse_ip_identifier_checked`, `select_challenge`, `build_http01_url`, `build_tls_alpn_san`, `prepare_csr_for_ip`.
   - Typed error model (`E_WrongType`, `E_Malformed`, `E_IPv4Mapped`, `E_DNS01Forbidden`, `E_SANMismatch`).
   - **Iff theorems** matching the JSONPath repo's API contract (e.g., `parse_checked_wrongtype_iff`, `select_challenge_dns01_iff`).
   - `Separate Extraction` block emitting OCaml for the API (mirroring `JPV_API_Extraction.v` style: `Set Extraction KeepSingleton`, `Extraction Inline` for hot paths, `Extraction Blacklist` for `String List Int Z`).

6. **`theories/RFC8738_PropertySuite.v`** — RFC examples + differential vectors.
   - All literal IP addresses appearing in RFC 8738 (§3 examples, §4.1 HTTP-01 URLs for `192.0.2.1` and `2001:db8::1`, §4.2 cert example, §8 reserved-range examples) verified via `vm_compute`.
   - Differential vectors for pathological forms: leading-zero IPv4 (`010.0.0.1`), uppercase IPv6, `::ffff:192.0.2.1` (rejected), all-zero `::`, single-zero non-compression `1:0:1:1:1:1:1:1`.
   - Aggregate theorem `property_suite_passes : full_suite = true` proven by `vm_compute. reflexivity.`.

7. **`theories/RFC8738.v`** — facade re-exporting all modules (`Require Export`).

8. **`README.md`** — repository overview, module layout, build instructions, extraction usage, citation block.

9. **Build hygiene**:
   - `make` runs end-to-end without warnings (currently emits the `From Coq` deprecation; resolve by switching to `From Stdlib` once the JSONPath repo also moves).
   - `make proof-hygiene` passes (no `Admitted`, no `Axiom`).
   - `make path-hygiene` passes.

10. **CI scaffolding**:
    - `.github/workflows/build.yml` running `coqc` against the Rocq 9 toolchain.
    - The existing `path-hygiene.yml` already runs.

11. **Optional stretch goals** (not strictly required for "true formalization" but a complete repo would have):
    - Symbolic IPv6 round-trip theorem `parse_ipv6 (print_ipv6 ip) = Some ip` for all valid `ip` (currently covered by `vm_compute` examples; full symbolic proof requires ~1500–2500 LoC of zero-run-compression reasoning, which is out of proportion to the rest of the repo).
    - Bidirectional ABNF specification of the IP address grammar (RFC 5952 has an ABNF appendix that could be mechanically reflected).
    - Coq → C++ extraction via Crane (mirroring `demo/crane-cli` from `jsonpath-verified`).
    - QuickChick property tests for randomized IP inputs.
