def parse_int(buf, sz):
    if len(buf) < 2*sz:
        raise ValueError("parse_int: buf too short")
    return (int(buf[:2*sz], 16), buf[2*sz:])

def parse_opaque(buf, sz):
    (array_length, buf) = parse_int(buf, sz)
    if len(buf) < 2*array_length:
        raise ValueError("parse_opaque: buf too short")
    return (buf[:2*array_length], buf[2*array_length:])

def parse_array(buf, sz, parser):
    (data, buf) = parse_opaque(buf, sz)
    result = []
    while len(data) != 0:
        (cur, data) = parser(data)
        result.append(cur)
    return (result, buf)

def parse_optional(buf, parser):
    (b, buf) = parse_int(buf, 1)
    if b == 0:
        return (None, buf)
    elif b == 1:
        return parser(buf)
    else:
        raise ValueError("parse_optional: bad boolean")

def parse_parent_node(buf):
    (hpke_pk, buf) = parse_opaque(buf, 2)
    (parent_hash, buf) = parse_opaque(buf, 1)
    (unmerged_leaves, buf) = parse_array(buf, 4, lambda x: parse_int(x, 4))
    return ({
        "hpke_pk": hpke_pk,
        "parent_hash": parent_hash,
        "unmerged_leaves": unmerged_leaves
    }, buf)

def parse_credential(buf):
    (cred_type, buf) = parse_int(buf, 2)
    if cred_type != 1:
        raise ValueError("parse_credential: not basic type")
    (identity, buf) = parse_opaque(buf, 2)
    (signature_scheme, buf) = parse_int(buf, 2)
    (signature_key, buf) = parse_opaque(buf, 2)
    return ({
        "identity": identity,
        "signature_scheme": signature_scheme,
        "signature_key": signature_key,
    }, buf)

def parse_key_package(buf):
    (protocol_version, buf) = parse_int(buf, 1)
    (cipher_suite, buf) = parse_int(buf, 2)
    (hpke_pk, buf) = parse_opaque(buf, 2)
    (credential, buf) = parse_credential(buf)
    (extensions, buf) = parse_opaque(buf, 4)
    (signature, buf) = parse_opaque(buf, 2)
    return ({
        "protocol_version": protocol_version,
        "cipher_suite": cipher_suite,
        "hpke_pk": hpke_pk,
        "credential": credential,
        "extensions": extensions,
        "signature": signature,
    }, buf)

def parse_node(buf):
    (node_type, buf) = parse_int(buf, 1)
    if node_type == 1:
        return parse_key_package(buf)
    elif node_type == 2:
        return parse_parent_node(buf)
    else:
        raise ValueError("parse_node: unknown node type")

buf = input()
(ratchet_tree, buf) = parse_array(buf, 4, lambda x: parse_optional(x, parse_node))
print("\n".join(str(x) for x in ratchet_tree))
