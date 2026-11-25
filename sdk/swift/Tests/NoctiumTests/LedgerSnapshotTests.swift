import CryptoKit
import Foundation
import Noctium
import XCTest

final class LedgerSnapshotTests: XCTestCase {
    private let trustedManifestSHA256 = "3de4ada1aede5fe80791c4374f0ca223f29ff68c1b1377a26e611e427cbbf69f"

    func testCompactScalarListPagesAndDigestRejection() throws {
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

        let cases = try XCTUnwrap(manifest["cases"] as? [[String: Any]])
        let emptyCase = try pageCase(in: cases, snapshot: "empty", offset: 0)
        let firstCase = try pageCase(in: cases, snapshot: "populated", offset: 0)
        let continuationCase = try pageCase(in: cases, snapshot: "populated", offset: 2)

        let emptyPage = try page(
            plan: plan, planDigest: planDigest, snapshot: empty, stateDigest: emptyDigest, fixtureCase: emptyCase
        )
        try assertPage(emptyPage, matches: emptyCase)

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
    }

    private func page(
        plan: Data,
        planDigest: String,
        snapshot: Data,
        stateDigest: String,
        fixtureCase: [String: Any],
        offset: Int? = nil
    ) throws -> Data {
        let pageOffset = try offset ?? integer("offset", in: fixtureCase)
        let limit = try integer("limit", in: fixtureCase)
        return try LedgerSnapshot.collectionPage(
            request: request(
                planSHA256: planDigest,
                stateSHA256: stateDigest,
                offset: pageOffset,
                limit: limit
            ),
            plan: plan,
            snapshot: snapshot
        )
    }

    private func request(planSHA256: String, stateSHA256: String, offset: Int, limit: Int) throws -> Data {
        try JSONSerialization.data(withJSONObject: [
            "abiVersion": 1,
            "planSha256": planSHA256,
            "stateSha256": stateSHA256,
            "name": "values",
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

    private func pageCase(in cases: [[String: Any]], snapshot: String, offset: Int) throws -> [String: Any] {
        try XCTUnwrap(cases.first {
            $0["snapshot"] as? String == snapshot && $0["name"] as? String == "values" &&
                (($0["offset"] as? NSNumber)?.intValue == offset)
        })
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
