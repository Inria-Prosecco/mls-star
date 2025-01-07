module MLS.TreeKEM.API.KeySchedule.Types

// All the keys that are not forward-secret within an epoch.
// In particular, encryption_secret is not in this set of keys:
// it is returned by the commit function

type epoch_keys (bytes:Type0) = {
  sender_data_secret: bytes;
  exporter_secret: bytes;
  external_secret: bytes;
  membership_key: bytes;
  resumption_psk: bytes;
  epoch_authenticator: bytes;
  confirmation_tag: bytes;
}

type treekem_keyschedule_state (bytes:Type0) = {
  epoch_keys: epoch_keys bytes;
  init_secret: bytes;
}
