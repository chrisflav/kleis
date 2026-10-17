# The CalDAV extension

Calendars through kleis, with the standard clients: **vdirsyncer** keeps a local copy of every
calendar the account sees under `~/calendars/<server>/` and pushes changes back; **khal** reads
and edits that copy. kleis's setup (`/.kleis/v1/setup`) writes both clients' configuration, with
placeholder credentials kleis replaces with the account's.

```sh
yes | vdirsyncer discover      # once: find the server's calendars
vdirsyncer sync                # before reading, and after every change
vdirsyncer metasync            # calendar names and colours
khal printcalendars
khal list today 7d
khal new -a "Personal" 2031-03-04 10:00 11:00 "Dentist" :: "notes"
khal edit "Dentist"
```

A conflict — the same event changed on the server and locally — is resolved in the server's favour
(`conflict_resolution = "a wins"`), so a person's edit is never overwritten. vdirsyncer refuses to
push a calendar that was emptied entirely (`--force-delete` would), which is a safeguard worth
keeping.

## An account

`<user>:<password>` — for Nextcloud an app password — bound to the server's host:

```toml
name        = "caldav/secretary@cloud.example.org"
service     = "caldav"
hosts       = ["cloud.example.org"]
secret_file = "/run/secrets/caldav-secretary"
```

## A spec

Read anything; write and delete events — never whole calendars — only under the account's own
calendar home. The extension claims the whole host, so for a Nextcloud server the path bound also
keeps a "write" from being a file upload:

```
account caldav/secretary@cloud.example.org
  allow read
  allow write, delete where path starts_with "remote.php/dav/calendars/secretary/" and path ends_with ".ics"
```

Calendars shared with that user appear under its home (`…/calendars/secretary/<name>_shared_by_<owner>/`),
and the server records every change as that user's.

## Testing

`test/vdirsyncer-e2e.sh` runs Radicale and kleis (`kleis:master`) in docker, writes the setup files
into a scratch home, and drives vdirsyncer and khal through kleis: discover, sync, create, list,
delete, and the spec's refusals.
