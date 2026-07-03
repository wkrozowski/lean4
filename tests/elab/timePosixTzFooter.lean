import Std.Time
open Std.Time

/-!
Tests for DST transitions governed by the POSIX TZ footer in TZif files
(timestamps beyond the last explicit TZIF transition entry). Each pair tests
one second before and at the transition instant in a distinct timezone.
All expected values are verified against Python's `zoneinfo` module.
-/

#guard
  match TimeZone.parsePosixTz "UTC0" with
  | .ok rule => rule.dst.isNone
  | .error _ => false

#guard
  match TimeZone.parsePosixTz "EST5EDT,M3.2.0,M11.1.0" with
  | .ok rule =>
    match rule.dst with
    | some dst =>
      dst.name == "EDT" &&
        dst.offset.second.val == -14400 &&
        dst.start.isSome &&
        dst.end_.isSome
    | none => false
  | .error _ => false

-- America/New_York: EST5EDT,M3.2.0,M11.1.0  (spring forward 2038-03-14)
/-- info: zoned("2038-03-14T01:59:59.000000000-05:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "America/New_York"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152162799) zr

/-- info: zoned("2038-03-14T03:00:00.000000000-04:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "America/New_York"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152162800) zr

-- America/Chicago: CST6CDT,M3.2.0,M11.1.0  (spring forward 2038-03-14)
/-- info: zoned("2038-03-14T01:59:59.000000000-06:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "America/Chicago"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152166399) zr

/-- info: zoned("2038-03-14T03:00:00.000000000-05:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "America/Chicago"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152166400) zr

-- America/Denver: MST7MDT,M3.2.0,M11.1.0  (spring forward 2038-03-14)
/-- info: zoned("2038-03-14T01:59:59.000000000-07:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "America/Denver"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152169999) zr

/-- info: zoned("2038-03-14T03:00:00.000000000-06:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "America/Denver"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152170000) zr

-- America/Los_Angeles: PST8PDT,M3.2.0,M11.1.0  (spring forward 2038-03-14)
/-- info: zoned("2038-03-14T01:59:59.000000000-08:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "America/Los_Angeles"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152173599) zr

/-- info: zoned("2038-03-14T03:00:00.000000000-07:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "America/Los_Angeles"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152173600) zr

-- America/Anchorage: AKST9AKDT,M3.2.0,M11.1.0  (spring forward 2038-03-14)
/-- info: zoned("2038-03-14T01:59:59.000000000-09:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "America/Anchorage"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152177199) zr

/-- info: zoned("2038-03-14T03:00:00.000000000-08:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "America/Anchorage"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152177200) zr

-- America/Halifax: AST4ADT,M3.2.0,M11.1.0  (spring forward 2038-03-14)
/-- info: zoned("2038-03-14T01:59:59.000000000-04:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "America/Halifax"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152159199) zr

/-- info: zoned("2038-03-14T03:00:00.000000000-03:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "America/Halifax"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152159200) zr

-- America/Havana: CST5CDT,M3.2.0/0,M10.5.0/1  (springs forward at midnight 2038-03-14)
/-- info: zoned("2038-03-13T23:59:59.000000000-05:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "America/Havana"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152155599) zr

/-- info: zoned("2038-03-14T01:00:00.000000000-04:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "America/Havana"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2152155600) zr

-- Europe/London: GMT0BST,M3.5.0/1,M10.5.0  (spring forward 2038-03-28)
/-- info: zoned("2038-03-28T00:59:59.000000000Z") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Europe/London"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153350799) zr

/-- info: zoned("2038-03-28T02:00:00.000000000+01:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Europe/London"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153350800) zr

-- Europe/Paris: CET-1CEST,M3.5.0,M10.5.0/3  (spring forward 2038-03-28)
/-- info: zoned("2038-03-28T01:59:59.000000000+01:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Europe/Paris"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153350799) zr

/-- info: zoned("2038-03-28T03:00:00.000000000+02:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Europe/Paris"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153350800) zr

-- Europe/Helsinki: EET-2EEST,M3.5.0/3,M10.5.0/4  (spring forward 2038-03-28)
/-- info: zoned("2038-03-28T02:59:59.000000000+02:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Europe/Helsinki"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153350799) zr

/-- info: zoned("2038-03-28T04:00:00.000000000+03:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Europe/Helsinki"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153350800) zr

-- Atlantic/Azores: -01+00,M3.5.0/0,M10.5.0/1  (spring forward 2038-03-28)
/-- info: zoned("2038-03-27T23:59:59.000000000-01:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Atlantic/Azores"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153350799) zr

/-- info: zoned("2038-03-28T01:00:00.000000000Z") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Atlantic/Azores"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153350800) zr

-- Asia/Jerusalem: IST-2IDT,M3.4.4/26,M10.5.0  (spring forward 2038-03-26)
/-- info: zoned("2038-03-26T01:59:59.000000000+02:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Asia/Jerusalem"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153174399) zr

/-- info: zoned("2038-03-26T03:00:00.000000000+03:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Asia/Jerusalem"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153174400) zr

-- Asia/Beirut: EET-2EEST,M3.5.0/0,M10.5.0/0  (spring forward 2038-03-28 at midnight)
/-- info: zoned("2038-03-27T23:59:59.000000000+02:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Asia/Beirut"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153339999) zr

/-- info: zoned("2038-03-28T01:00:00.000000000+03:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Asia/Beirut"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153340000) zr

-- Africa/Cairo: EET-2EEST,M4.5.5/0,M10.5.5/24  (spring forward 2038-04-30)
/-- info: zoned("2038-04-29T23:59:59.000000000+02:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Africa/Cairo"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2156191199) zr

/-- info: zoned("2038-04-30T01:00:00.000000000+03:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Africa/Cairo"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2156191200) zr

-- Australia/Sydney: AEST-10AEDT,M10.1.0,M4.1.0/3  (fall back 2038-04-04)
/-- info: zoned("2038-04-04T02:59:59.000000000+11:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Australia/Sydney"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153923199) zr

/-- info: zoned("2038-04-04T02:00:00.000000000+10:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Australia/Sydney"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153923200) zr

-- Australia/Lord_Howe: +1030-11,M10.1.0,M4.1.0  (30-min fall back 2038-04-04)
/-- info: zoned("2038-04-04T01:59:59.000000000+11:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Australia/Lord_Howe"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153919599) zr

/-- info: zoned("2038-04-04T01:30:00.000000000+10:30") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Australia/Lord_Howe"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153919600) zr

-- Pacific/Auckland: NZST-12NZDT,M9.5.0,M4.1.0/3  (fall back 2038-04-04)
/-- info: zoned("2038-04-04T02:59:59.000000000+13:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Pacific/Auckland"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153915999) zr

/-- info: zoned("2038-04-04T02:00:00.000000000+12:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Pacific/Auckland"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153916000) zr

-- Pacific/Chatham: +1245-1345,M9.5.0/2:45,M4.1.0/3:45  (fall back 2038-04-04, +45min offset)

/-- info: zoned("2038-04-04T03:44:59.000000000+13:45") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Pacific/Chatham"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153915999) zr

/-- info: zoned("2038-04-04T02:45:00.000000000+12:45") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "Pacific/Chatham"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153916000) zr

-- America/Santiago: -04-03,M9.1.6/24,M4.1.6/24  (fall back 2038-04-04 Southern Hemisphere)
/-- info: zoned("2038-04-03T23:59:59.000000000-03:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "America/Santiago"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153962799) zr

/-- info: zoned("2038-04-03T23:00:00.000000000-04:00") -/
#guard_msgs in
#eval show IO _ from do
  let zr ← Database.defaultGetZoneRules "America/Santiago"
  return DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch 2153962800) zr
