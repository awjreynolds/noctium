import CNoctium
import Foundation

public enum LedgerSnapshot {
    /// A typed page from a Map<Field, Bool> in the supplied public plan.
    public struct FieldBoolMapPage: Decodable {
        public struct Entry: Decodable {
            /// The canonical Field decimal returned by the native collection reader.
            public let key: String
            public let value: Bool
        }

        public let entries: [Entry]
        /// The offset for the next page, or nil when this page ends the map.
        public let nextOffset: Int?

        private enum CodingKeys: String, CodingKey {
            case abiVersion
            case kind
            case entries
            case nextOffset
        }

        public init(from decoder: Decoder) throws {
            let container = try decoder.container(keyedBy: CodingKeys.self)
            let abiVersion = try container.decode(Int.self, forKey: .abiVersion)
            let kind = try container.decode(String.self, forKey: .kind)
            guard abiVersion == 1, kind == "map" else {
                throw WitnessSession.Failure.invalidResult
            }
            entries = try container.decode([Entry].self, forKey: .entries)
            nextOffset = try container.decode(Int?.self, forKey: .nextOffset)
        }
    }

    public static func collectionPage(request: Data, plan: Data, snapshot: Data) throws -> Data {
        var token: UInt64 = 0
        let status = request.withBytePointer { requestBytes, requestSize in
            plan.withBytePointer { planBytes, planSize in
                snapshot.withBytePointer { snapshotBytes, snapshotSize in
                    noctium_ledger_collection_page(
                        requestBytes, requestSize,
                        planBytes, planSize,
                        snapshotBytes, snapshotSize,
                        &token
                    )
                }
            }
        }
        try WitnessSession.check(status)
        return try takeNativeResult(token)
    }

    /// Reads a page and decodes its entries for a Map<Field, Bool> in the public plan.
    public static func fieldBoolMapPage(
        request: Data,
        plan: Data,
        snapshot: Data
    ) throws -> FieldBoolMapPage {
        let result = try collectionPage(request: request, plan: plan, snapshot: snapshot)
        return try JSONDecoder().decode(FieldBoolMapPage.self, from: result)
    }
}
