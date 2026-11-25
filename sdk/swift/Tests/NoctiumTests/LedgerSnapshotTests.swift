import CryptoKit
import Foundation
import Noctium
import XCTest

final class LedgerSnapshotTests: XCTestCase {
    private let trustedManifestSHA256 = "3de4ada1aede5fe80791c4374f0ca223f29ff68c1b1377a26e611e427cbbf69f"

    func testCompactCollectionPagesAndDigestRejection() throws {
        let root = try XCTUnwrap(Bundle.module.resourceURL?.appendingPathComponent("Fixtures", isDirectory: true))
        let manifestBytes = try resource("manifest.json", in: root)
        XCTAssertEqual(sha256(manifestBytes), trustedManifestSHA256)

        let manifest = try XCTUnwrap(JSONSerialization.jsonObject(with: manifestBytes) as? [String: Any])
        XCTAssertEqual(manifest["schemaVersion"] as? Int, 1)
        let planEntry = try dictionary(manifest["plan"])
        let planDigest = try string("sha256", in: planEntry)
        let plan = try resource(string("file", in: planEntry), in: root)
        XCTAssertEqual(sha256(plan), planDigest)

        let snapshotEntries = try dictionary(manifest["snapshots"])
        let emptyEntry = try dictionary(snapshotEntries["empty"])
        let emptyDigest = try string("sha256", in: emptyEntry)
        let empty = try resource(string("file", in: emptyEntry), in: root)
        XCTAssertEqual(sha256(empty), emptyDigest)
        let populatedEntry = try dictionary(snapshotEntries["populated"])
        let populatedDigest = try string("sha256", in: populatedEntry)
        let populated = try resource(string("file", in: populatedEntry), in: root)
        XCTAssertEqual(sha256(populated), populatedDigest)
        let removedEntry = try dictionary(snapshotEntries["removed"])
        let removedDigest = try string("sha256", in: removedEntry)
        let removed = try resource(string("file", in: removedEntry), in: root)
        XCTAssertEqual(sha256(removed), removedDigest)

        let cases = try XCTUnwrap(manifest["cases"] as? [[String: Any]])
        let emptyCase = try pageCase(in: cases, snapshot: "empty", offset: 0)
        let emptyMembersCase = try pageCase(in: cases, snapshot: "empty", offset: 0, name: "members")
        let firstCase = try pageCase(in: cases, snapshot: "populated", offset: 0)
        let continuationCase = try pageCase(in: cases, snapshot: "populated", offset: 2)

        let emptyPage = try page(
            plan: plan, planDigest: planDigest, snapshot: empty, stateDigest: emptyDigest, fixtureCase: emptyCase
        )
        try assertPage(emptyPage, matches: emptyCase)

        let emptyMembers = try page(
            plan: plan, planDigest: planDigest, snapshot: empty, stateDigest: emptyDigest,
            fixtureCase: emptyMembersCase, name: "members"
        )
        let emptyMembersPage = try setPage(emptyMembers)
        try assertSetPage(emptyMembersPage, matches: emptyMembersCase)

        let firstPage = try page(
            plan: plan, planDigest: planDigest, snapshot: populated,
            stateDigest: populatedDigest, fixtureCase: firstCase
        )
        try assertPage(firstPage, matches: firstCase)
        let firstPageJSON = try jsonObject(firstPage)
        let returnedOffset = try integer("nextOffset", in: firstPageJSON)
        XCTAssertEqual(returnedOffset, 2)
        let continuationOffset = try integer("offset", in: continuationCase)
        XCTAssertEqual(returnedOffset, continuationOffset)

        let continuation = try page(
            plan: plan, planDigest: planDigest, snapshot: populated,
            stateDigest: populatedDigest, fixtureCase: continuationCase, offset: returnedOffset
        )
        try assertPage(continuation, matches: continuationCase)

        let firstMembersCase = try pageCase(in: cases, snapshot: "populated", offset: 0, name: "members")
        let membersContinuationCase = try pageCase(in: cases, snapshot: "populated", offset: 2, name: "members")
        let firstMembers = try page(
            plan: plan, planDigest: planDigest, snapshot: populated, stateDigest: populatedDigest,
            fixtureCase: firstMembersCase, name: "members"
        )
        let firstMembersPage = try setPage(firstMembers)
        try assertSetPage(firstMembersPage, matches: firstMembersCase)
        let membersContinuationOffset = try XCTUnwrap(firstMembersPage.nextOffset)
        XCTAssertEqual(membersContinuationOffset, try integer("offset", in: membersContinuationCase))

        let membersContinuation = try page(
            plan: plan, planDigest: planDigest, snapshot: populated, stateDigest: populatedDigest,
            fixtureCase: membersContinuationCase, offset: membersContinuationOffset, name: "members"
        )
        let membersContinuationPage = try setPage(membersContinuation)
        try assertSetPage(membersContinuationPage, matches: membersContinuationCase)

        let joinedMembers = firstMembersPage.entries + membersContinuationPage.entries
        let compactMembers = try [firstMembersCase, membersContinuationCase].flatMap { fixtureCase in
            try setPage(fixtureCase).entries.map(\.values)
        }
        XCTAssertEqual(joinedMembers.map(\.values), compactMembers)

        let removedMembersCase = try pageCase(in: cases, snapshot: "removed", offset: 0, name: "members")
        let removedMembers = try page(
            plan: plan, planDigest: planDigest, snapshot: removed, stateDigest: removedDigest,
            fixtureCase: removedMembersCase, name: "members"
        )
        let removedMembersPage = try setPage(removedMembers)
        try assertSetPage(removedMembersPage, matches: removedMembersCase)
        XCTAssertEqual(
            removedMembersPage.entries.map(\.values),
            [[UInt8](repeating: 1, count: 32), [UInt8](repeating: 9, count: 32)]
        )

        let firstFlagsCase = try pageCase(in: cases, snapshot: "populated", offset: 0, name: "flags")
        let firstFlagsPage = try LedgerSnapshot.fieldBoolMapPage(
            request: request(
                planSHA256: planDigest,
                stateSHA256: populatedDigest,
                offset: try integer("offset", in: firstFlagsCase),
                limit: try integer("limit", in: firstFlagsCase),
                name: "flags"
            ),
            plan: plan,
            snapshot: populated
        )
        XCTAssertEqual(firstFlagsPage.entries.count, 2)

        let flagsContinuationOffset = try XCTUnwrap(firstFlagsPage.nextOffset)
        let firstFlagsExpected = try dictionary(firstFlagsCase["expected"])
        XCTAssertEqual(flagsContinuationOffset, try integer("nextOffset", in: firstFlagsExpected))
        let flagsContinuationCase = try pageCase(
            in: cases, snapshot: "populated", offset: flagsContinuationOffset, name: "flags"
        )
        let flagsContinuationPage = try LedgerSnapshot.fieldBoolMapPage(
            request: request(
                planSHA256: planDigest,
                stateSHA256: populatedDigest,
                offset: flagsContinuationOffset,
                limit: try integer("limit", in: flagsContinuationCase),
                name: "flags"
            ),
            plan: plan,
            snapshot: populated
        )
        XCTAssertEqual(flagsContinuationPage.entries.count, 1)
        XCTAssertNil(flagsContinuationPage.nextOffset)

        let joinedFlagsEntries = firstFlagsPage.entries + flagsContinuationPage.entries
        let oracleFlagsCases = [firstFlagsCase, flagsContinuationCase]
        let oracleFlagsEntries = try oracleFlagsCases.flatMap { fixtureCase in
            let expected = try dictionary(fixtureCase["expected"])
            let entries = try XCTUnwrap(expected["entries"] as? [[String: Any]])
            return try entries.map { entry in
                (
                    key: try string("key", in: entry),
                    value: try XCTUnwrap(entry["value"] as? Bool)
                )
            }
        }
        XCTAssertEqual(joinedFlagsEntries.map(\.key), oracleFlagsEntries.map(\.key))
        XCTAssertEqual(joinedFlagsEntries.map(\.value), oracleFlagsEntries.map(\.value))

        let firstByte = populatedDigest.first == "0" ? "1" : "0"
        let alteredDigest = firstByte + String(populatedDigest.dropFirst())
        XCTAssertThrowsError(try LedgerSnapshot.collectionPage(
            request: request(
                planSHA256: planDigest,
                stateSHA256: alteredDigest,
                offset: 0,
                limit: 2
            ),
            plan: plan,
            snapshot: populated
        )) {
            XCTAssertEqual($0 as? WitnessSession.Failure, .nativeStatus(1))
        }

        XCTAssertThrowsError(try LedgerSnapshot.fieldBoolMapPage(
            request: request(
                planSHA256: planDigest,
                stateSHA256: alteredDigest,
                offset: 0,
                limit: 2,
                name: "flags"
            ),
            plan: plan,
            snapshot: populated
        )) {
            XCTAssertEqual($0 as? WitnessSession.Failure, .nativeStatus(1))
        }

        XCTAssertThrowsError(try LedgerSnapshot.collectionPage(
            request: request(
                planSHA256: planDigest,
                stateSHA256: String(repeating: "0", count: 63),
                offset: 0,
                limit: 2
            ),
            plan: plan,
            snapshot: populated
        )) {
            XCTAssertEqual($0 as? WitnessSession.Failure, .nativeStatus(1))
        }

        let malformedSnapshot = Data(populated.prefix(8))
        XCTAssertEqual(malformedSnapshot.count, 8)
        XCTAssertThrowsError(try LedgerSnapshot.collectionPage(
            request: request(
                planSHA256: planDigest,
                stateSHA256: sha256(malformedSnapshot),
                offset: 0,
                limit: 2,
                name: "members"
            ),
            plan: plan,
            snapshot: malformedSnapshot
        )) {
            XCTAssertEqual($0 as? WitnessSession.Failure, .nativeStatus(1))
        }
    }

    private func page(
        plan: Data,
        planDigest: String,
        snapshot: Data,
        stateDigest: String,
        fixtureCase: [String: Any],
        offset: Int? = nil,
        name: String = "values"
    ) throws -> Data {
        let pageOffset = try offset ?? integer("offset", in: fixtureCase)
        let limit = try integer("limit", in: fixtureCase)
        return try LedgerSnapshot.collectionPage(
            request: request(
                planSHA256: planDigest,
                stateSHA256: stateDigest,
                offset: pageOffset,
                limit: limit,
                name: name
            ),
            plan: plan,
            snapshot: snapshot
        )
    }

    private func request(
        planSHA256: String,
        stateSHA256: String,
        offset: Int,
        limit: Int,
        name: String = "values"
    ) throws -> Data {
        try JSONSerialization.data(withJSONObject: [
            "abiVersion": 1,
            "planSha256": planSHA256,
            "stateSha256": stateSHA256,
            "name": name,
            "keys": [],
            "offset": offset,
            "limit": limit,
        ], options: [.sortedKeys])
    }

    private func assertPage(
        _ actual: Data,
        matches fixtureCase: [String: Any],
        file: StaticString = #filePath,
        line: UInt = #line
    ) throws {
        let expected = try dictionary(fixtureCase["expected"])
        XCTAssertEqual(
            try jsonObject(actual) as NSDictionary,
            expected as NSDictionary,
            file: file,
            line: line
        )
    }

    private func assertSetPage(
        _ actual: SetPage,
        matches fixtureCase: [String: Any],
        file: StaticString = #filePath,
        line: UInt = #line
    ) throws {
        let expected = try setPage(fixtureCase)
        XCTAssertEqual(actual.abiVersion, expected.abiVersion, file: file, line: line)
        XCTAssertEqual(actual.kind, expected.kind, file: file, line: line)
        XCTAssertEqual(actual.nextOffset, expected.nextOffset, file: file, line: line)
        XCTAssertEqual(actual.entries.count, expected.entries.count, file: file, line: line)
        XCTAssertEqual(actual.kind, "set", file: file, line: line)
        XCTAssertEqual(actual.entries.map(\.kind), Array(repeating: "bytes", count: expected.entries.count), file: file, line: line)
        XCTAssertEqual(actual.entries.map(\.values), expected.entries.map(\.values), file: file, line: line)
        XCTAssertTrue(actual.entries.allSatisfy { $0.values.count == 32 }, file: file, line: line)
    }

    private func setPage(_ data: Data) throws -> SetPage {
        try JSONDecoder().decode(SetPage.self, from: data)
    }

    private func setPage(_ fixtureCase: [String: Any]) throws -> SetPage {
        let expected = try dictionary(fixtureCase["expected"])
        let data = try JSONSerialization.data(withJSONObject: expected, options: [.sortedKeys])
        return try setPage(data)
    }

    private func pageCase(
        in cases: [[String: Any]],
        snapshot: String,
        offset: Int,
        name: String = "values"
    ) throws -> [String: Any] {
        try XCTUnwrap(cases.first {
            $0["snapshot"] as? String == snapshot && $0["name"] as? String == name &&
                (($0["offset"] as? NSNumber)?.intValue == offset)
        })
    }

    private struct SetPage: Decodable {
        struct Entry: Decodable {
            let kind: String
            let values: [UInt8]
        }

        let abiVersion: Int
        let kind: String
        let entries: [Entry]
        let nextOffset: Int?
    }

    private func jsonObject(_ data: Data) throws -> [String: Any] {
        try XCTUnwrap(JSONSerialization.jsonObject(with: data) as? [String: Any])
    }

    private func dictionary(_ value: Any?) throws -> [String: Any] {
        try XCTUnwrap(value as? [String: Any])
    }

    private func string(_ key: String, in object: [String: Any]) throws -> String {
        try XCTUnwrap(object[key] as? String)
    }

    private func integer(_ key: String, in object: [String: Any]) throws -> Int {
        try XCTUnwrap((object[key] as? NSNumber)?.intValue)
    }

    private func resource(_ name: String, in root: URL) throws -> Data {
        try Data(contentsOf: root.appendingPathComponent(name))
    }

    private func sha256(_ data: Data) -> String {
        SHA256.hash(data: data).map { String(format: "%02x", $0) }.joined()
    }
}
