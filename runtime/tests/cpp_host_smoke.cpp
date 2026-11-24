#include "smoke_helpers.hpp"
#include <iostream>
#include <map>
#include <tuple>

using JsonCall = int32_t (*)(uint64_t, const uint8_t *, size_t, uint64_t *);
static const std::string staged_value = "8675309";
static std::string checked_take(uint64_t token) {
  const auto result = take(token);
  assert(!contains(result, staged_value));
  assert(!contains(result, "claims/"));
  assert(!contains(result,"journalDigest"));
  assert(!contains(result,"8675310"));
  return result;
}
static std::string host_call(uint64_t session, const std::string &json, JsonCall function,
                             int32_t expected = NOCTIUM_OK) {
  uint64_t result = 99;
  assert(function(session, reinterpret_cast<const uint8_t *>(json.data()), json.size(), &result) == expected);
  if (expected != NOCTIUM_OK) { assert(result == 0); return {}; }
  return checked_take(result);
}
static std::string host_advance(uint64_t session) {
  uint64_t result = 0;
  assert(noctium_session_advance(session, &result) == NOCTIUM_OK);
  return checked_take(result);
}
static std::string private_data(uint64_t session, uint32_t kind, int32_t expected = NOCTIUM_OK) {
  uint64_t token = 99;
  assert(noctium_session_private_data(session, kind, &token) == expected);
  if (expected != NOCTIUM_OK) { assert(token == 0); return {}; }
  size_t length = 0, written = 99;
  assert(noctium_result_length(token, &length) == NOCTIUM_INVALID_HANDLE);
  assert(noctium_private_length(token, &length) == NOCTIUM_OK);
  std::string bytes(length, '\0');
  assert(noctium_private_copy(token, reinterpret_cast<uint8_t *>(bytes.data()), length - 1, &written) == NOCTIUM_BUFFER_TOO_SMALL);
  assert(written == 0);
  assert(noctium_private_copy(token, reinterpret_cast<uint8_t *>(bytes.data()), length, &written) == NOCTIUM_OK);
  assert(noctium_private_free(token) == NOCTIUM_OK);
  assert(noctium_private_free(token) == NOCTIUM_INVALID_HANDLE);
  return bytes;
}
static std::string notice(uint64_t session, char attempt, char transaction, const std::string &event,
                          int32_t expected = NOCTIUM_OK) {
  return host_call(session, "{\"abiVersion\":1,\"event\":\"" + event +
    "\",\"attemptId\":\"" + std::string(64, attempt) + "\",\"transactionId\":\"" +
    std::string(64, transaction) + "\"}", noctium_session_notify, expected);
}
static std::string stage(uint64_t session, const std::string &key,
                         int32_t expected = NOCTIUM_OK,const std::string &value=staged_value) {
  return host_call(session, "{\"abiVersion\":1,\"operation\":\"private_state.stage.v1\",\"capability\":\"store\",\"key\":\"" +
    key + "\",\"type\":\"Native\",\"value\":\"" + value + "\"}", noctium_session_stage_private, expected);
}
static std::string read_response(uint64_t session, const std::string &value, int32_t expected = NOCTIUM_OK,
                                 const std::string &op = "private_state.read.v1", const std::string &cap = "store",
                                 const std::string &schema = "UIntRange<256>", unsigned id = 1) {
  return host_call(session, "{\"abiVersion\":1,\"requestId\":" + std::to_string(id) +
    ",\"operation\":\"" + op + "\",\"capability\":\"" + cap + "\",\"schema\":\"" + schema +
    "\",\"value\":" + value + "}", noctium_session_resume, expected);
}
static std::string field(const std::string &json,const std::string &key){
  const auto prefix="\""+key+"\":\"";const auto start=json.find(prefix);assert(start!=std::string::npos);
  const auto value=start+prefix.size();const auto end=json.find('"',value);assert(end!=std::string::npos);return json.substr(value,end-value);
}
static std::string cas_payload(uint64_t session,const std::string &outcome,const std::string &revision,const std::string &base="r0"){
  const auto journal=private_data(session,NOCTIUM_PRIVATE_JOURNAL);
  return "{\"abiVersion\":1,\"requestId\":3,\"operation\":\"private_state.compare_exchange.v1\",\"capability\":\"store\",\"schema\":\"PrivateStateCasResult/v1\",\"value\":{\"outcome\":\""+outcome+"\",\"baseRevision\":\""+base+"\",\"revision\":\""+revision+"\",\"attemptId\":\""+field(journal,"attemptId")+"\",\"transactionId\":\""+field(journal,"transactionId")+"\",\"journalDigest\":\""+field(journal,"journalDigest")+"\"}}";
}
static std::string commit_response(uint64_t session,const std::string &outcome,const std::string &revision,int32_t expected=NOCTIUM_OK,const std::string &base="r0"){
  const auto payload=expected==NOCTIUM_INVALID_STATE?"{\"abiVersion\":1,\"requestId\":3,\"value\":{}}":cas_payload(session,outcome,revision,base);
  return host_call(session,payload,noctium_session_resume,expected);
}
static std::string read_file(const char *path) {
  std::ifstream file(path);
  return std::string((std::istreambuf_iterator<char>(file)), {});
}
static std::vector<std::string> split_tabs(const std::string &line) {
  std::vector<std::string> fields;
  size_t start = 0;
  while (true) {
    const auto end = line.find('\t', start);
    fields.push_back(line.substr(start, end - start));
    if (end == std::string::npos) return fields;
    start = end + 1;
  }
}
struct HostCasCase {
  std::string name, after, expected;
  std::map<std::string, std::string> overrides;
};
struct HostCasCorpus {
  std::string version;
  std::map<std::string, std::string> pending;
  std::vector<HostCasCase> cases;
};
static HostCasCorpus read_host_cas_corpus(std::istream &input) {
  HostCasCorpus corpus;
  std::string line;
  assert(std::getline(input, line));
  const auto header = split_tabs(line);
  assert(header.size() == 2 && header[0] == "VERSION");
  corpus.version = header[1];
  assert(std::getline(input, line));
  const auto pending = split_tabs(line);
  const std::vector<std::string> pending_keys = {
      "requestId", "operation", "capability", "schema", "attemptId",
      "transactionId", "journalDigest", "baseRevision"};
  assert(pending.size() == pending_keys.size() + 1 && pending[0] == "PENDING");
  for (size_t i = 0; i < pending_keys.size(); ++i)
    corpus.pending.emplace(pending_keys[i], pending[i + 1]);
  while (std::getline(input, line)) {
    if (line.empty()) continue;
    const auto row = split_tabs(line);
    assert(row.size() >= 4 && row[0] == "CASE" && (row.size() - 4) % 2 == 0);
    HostCasCase item{row[1], row[2], row[3], {}};
    for (size_t i = 4; i < row.size(); i += 2)
      assert(item.overrides.emplace(row[i], row[i + 1]).second);
    corpus.cases.push_back(std::move(item));
  }
  return corpus;
}
static std::string json_string(const std::string &value) {
  std::string encoded = "\"";
  for (const char ch : value) {
    if (ch == '"' || ch == '\\') encoded += '\\';
    if (ch == '\n') encoded += "\\n";
    else if (ch == '\r') encoded += "\\r";
    else if (ch == '\t') encoded += "\\t";
    else encoded += ch;
  }
  encoded += '"';
  return encoded;
}
static std::string case_value(const HostCasCase &test_case,
                              const std::string &key,
                              const std::string &fallback) {
  const auto found = test_case.overrides.find(key);
  return found == test_case.overrides.end() ? fallback : found->second;
}
static std::string cas_case_payload(uint64_t session,
                                    const std::map<std::string, std::string> &pending,
                                    const HostCasCase &test_case) {
  const auto journal = private_data(session, NOCTIUM_PRIVATE_JOURNAL);
  return "{\"abiVersion\":1,\"requestId\":" +
      case_value(test_case, "requestId", pending.at("requestId")) +
      ",\"operation\":" +
      case_value(test_case, "operation", json_string(pending.at("operation"))) +
      ",\"capability\":" +
      case_value(test_case, "capability", json_string(pending.at("capability"))) +
      ",\"schema\":" +
      case_value(test_case, "schema", json_string(pending.at("schema"))) +
      ",\"value\":{\"attemptId\":" +
      case_value(test_case, "attemptId", json_string(field(journal, "attemptId"))) +
      ",\"transactionId\":" +
      case_value(test_case, "transactionId", json_string(field(journal, "transactionId"))) +
      ",\"journalDigest\":" +
      case_value(test_case, "journalDigest", json_string(field(journal, "journalDigest"))) +
      ",\"baseRevision\":" +
      case_value(test_case, "baseRevision", json_string(field(journal, "baseRevision"))) +
      ",\"outcome\":" + case_value(test_case, "outcome", json_string("committed")) +
      ",\"revision\":" + case_value(test_case, "revision", json_string("r1")) + "}}";
}
static std::string configured(std::string envelope, std::string context, char attempt) {
  const auto marker = context.find(std::string(64, 'a')); assert(marker != std::string::npos);
  context.replace(marker, 64, std::string(64, attempt));
  const auto end = envelope.find_last_not_of(" \r\n\t"); assert(envelope[end] == '}');
  envelope.erase(end);
  return envelope + ",\"hostContext\":" + context + "}";
}
static uint64_t prepared(const std::string &envelope) {
  const auto session = start_session(envelope);
  private_data(session, NOCTIUM_PRIVATE_JOURNAL, NOCTIUM_INVALID_STATE);
  stage(session, "claims/used");
  const auto request = host_advance(session);
  assert(contains(request, "private_state.read.v1"));
  assert(contains(private_data(session, NOCTIUM_PRIVATE_REQUEST), "claims/secret"));
  read_response(session, "\"255\"");
  assert(contains(host_advance(session), "\"name\":\"right\""));
  resume(session, 2, "\"255\"", NOCTIUM_OK);
  assert(contains(host_advance(session), "\"status\":\"completed\""));
  private_data(session,NOCTIUM_PRIVATE_JOURNAL,NOCTIUM_INVALID_STATE);
  stage(session,"claims/used",NOCTIUM_INVALID_STATE);
  return session;
}
static std::string accepted(uint64_t session, char attempt, char transaction);
static void host_cas_corpus(const std::string &envelope,
                            const std::string &context,
                            std::istream &fixture_input) {
  const auto corpus = read_host_cas_corpus(fixture_input);
  const auto &pending = corpus.pending;
  const auto &cases = corpus.cases;
  assert(corpus.version == "1");
  assert(cases.size() == 15);
  assert(pending.at("requestId") == "3");
  assert(pending.at("operation") == "private_state.compare_exchange.v1");
  assert(pending.at("capability") == "store");
  assert(pending.at("schema") == "PrivateStateCasResult/v1");
  assert(pending.at("journalDigest") == "<redacted-journal-digest>");

  const auto with = [&](char attempt) {
    return configured(envelope, context, attempt);
  };
  const auto session = prepared(with('a'));
  const auto pending_request = accepted(session, 'a', 'b');
  const auto journal = private_data(session, NOCTIUM_PRIVATE_JOURNAL);
  const auto private_request = private_data(session, NOCTIUM_PRIVATE_REQUEST);
  assert(contains(pending_request, "\"id\":" + pending.at("requestId")));
  assert(contains(pending_request, "\"operation\":\"" + pending.at("operation") + "\""));
  assert(contains(pending_request, "\"capability\":\"" + pending.at("capability") + "\""));
  assert(contains(pending_request, "\"schema\":\"" + pending.at("schema") + "\""));
  assert(field(journal, "attemptId") == pending.at("attemptId"));
  assert(field(journal, "transactionId") == pending.at("transactionId"));
  assert(field(journal, "baseRevision") == pending.at("baseRevision"));
  assert(field(journal, "journalDigest") != pending.at("journalDigest"));

  std::string committed_payload, conflict_payload;
  uint64_t conflict_session = 0;
  unsigned pending_rejections = 0, commits = 0, conflicts = 0, duplicates = 0;
  for (const auto &test_case : cases) {
    const auto &name = test_case.name;
    const auto &after = test_case.after;
    const auto &expected = test_case.expected;
    const auto &overrides = test_case.overrides;
    if (expected == "pending") {
      assert(after.empty());
      host_call(session, cas_case_payload(session, pending, test_case),
                noctium_session_resume, NOCTIUM_INVALID_RESPONSE);
      assert(private_data(session, NOCTIUM_PRIVATE_REQUEST) == private_request);
      assert(private_data(session, NOCTIUM_PRIVATE_JOURNAL) == journal);
      assert(notice(session, 'a', 'b', "accepted") == pending_request);
      ++pending_rejections;
    } else if (expected == "committed") {
      assert(name == "valid-commit" && after.empty());
      committed_payload = cas_case_payload(session, pending, test_case);
      assert(field(committed_payload, "journalDigest") ==
             field(journal, "journalDigest"));
      const auto result = host_call(session, committed_payload,
                                    noctium_session_resume);
      assert(contains(result, "\"phase\":\"committed\""));
      assert(contains(result, "\"hostCasAcknowledged\":true"));
      ++commits;
    } else if (expected == "rejected") {
      assert(after == "committed" || after == "conflict");
      const auto &prior = after == "committed" ? committed_payload : conflict_payload;
      assert(!prior.empty());
      assert(overrides.size() == 2);
      const auto outcome = after == "committed" ? "\"committed\"" : "\"conflict\"";
      const auto revision = after == "committed" ? "\"r1\"" : "\"r2\"";
      assert(overrides.at("outcome") == outcome && overrides.at("revision") == revision);
      host_call(after == "committed" ? session : conflict_session, prior,
                noctium_session_resume, NOCTIUM_INVALID_STATE);
      ++duplicates;
    } else if (expected == "conflict") {
      assert(name == "valid-conflict" && after.empty());
      conflict_session = prepared(with('c'));
      accepted(conflict_session, 'c', 'd');
      conflict_payload = cas_case_payload(conflict_session, pending, test_case);
      const auto result = host_call(conflict_session, conflict_payload,
                                    noctium_session_resume);
      assert(contains(result, "\"phase\":\"conflicted\""));
      assert(contains(result, "\"hostCasAcknowledged\":false"));
      ++conflicts;
    } else {
      assert(false && "unknown shared host CAS expectation");
    }
  }
  assert(pending_rejections == 11 && commits == 1 && conflicts == 1 &&
         duplicates == 2);
  assert(noctium_session_free(session) == NOCTIUM_OK);
  assert(noctium_session_free(conflict_session) == NOCTIUM_OK);
}
static std::string accepted(uint64_t session, char attempt, char transaction) {
  notice(session, attempt, transaction, "bind");
  const auto journal=private_data(session,NOCTIUM_PRIVATE_JOURNAL);
  assert(contains(journal,staged_value)||contains(journal,"8675310"));
  notice(session, attempt, transaction, "submitted", NOCTIUM_INVALID_STATE);
  notice(session, attempt, transaction, "persisted");
  notice(session, attempt, transaction, "persisted");
  notice(session, attempt, transaction, "submitted");
  notice(session, attempt, transaction, "submitted");
  const auto request = notice(session, attempt, transaction, "accepted");
  assert(contains(request, "private_state.compare_exchange.v1"));
  return request;
}
struct HostStore {
  unsigned revision = 0, applies = 0;
  struct Receipt {char transaction;unsigned revision;std::string digest;};
  std::map<char, Receipt> receipts;
  std::map<std::string,std::string> values;
  std::string reply(uint64_t session, char attempt, char transaction) {
    const auto journal = private_data(session, NOCTIUM_PRIVATE_REQUEST);
    assert(contains(journal, "\"attemptId\":\"" + std::string(64, attempt) + "\""));
    assert(contains(journal, "\"transactionId\":\"" + std::string(64, transaction) + "\""));
    assert(contains(journal, "\"namespace\":\"wallet_A\""));
    assert(contains(journal, "\"baseRevision\":\"r0\""));
    assert(contains(journal, "\"entrypoint\":\"apply\""));
    const auto digest=field(journal,"journalDigest");
    if (receipts.count(attempt)) {
      const auto old = receipts.at(attempt);
      const auto outcome=old.transaction==transaction && old.digest==digest?"committed":"conflict";
      return cas_payload(session,outcome,"r"+std::to_string(old.revision));
    }
    if (revision != 0) return cas_payload(session, "conflict", "r" + std::to_string(revision));
    values["claims/used"]=staged_value;
    ++revision; ++applies; receipts[attempt] = {transaction, revision,digest};
    return cas_payload(session, "committed", "r" + std::to_string(revision));
  }
  std::string apply(uint64_t session,char attempt,char transaction){return host_call(session,reply(session,attempt,transaction),noctium_session_resume);}
};
int main(int argc, char **argv) {
  assert(argc == 3);
  const auto envelope = read_file(argv[1]), context = read_file(argv[2]);
  auto with = [&](char attempt) { return configured(envelope, context, attempt); };
  for(const auto &change:std::vector<std::tuple<std::string,std::string,int32_t>>{
      {"\"requests\":3","\"requests\":2",NOCTIUM_LIMIT},
      {"\"keyPrefix\":\"claims/\"","\"keyPrefix\":\"*\"",NOCTIUM_INVALID_ARGUMENT},
      {"\"keyPrefix\":\"claims/\"","\"keyPrefix\":\"claims//\"",NOCTIUM_INVALID_ARGUMENT},
      {"\"resultSchema\":\"UIntRange<256>\"","\"resultSchema\":\"Bool\"",NOCTIUM_INVALID_ARGUMENT},
      {"claims/secret","claims_evil/secret",NOCTIUM_INVALID_RESPONSE}}){
    auto invalid=context;const auto at=invalid.find(std::get<0>(change));assert(at!=std::string::npos);invalid.replace(at,std::get<0>(change).size(),std::get<1>(change));
    const auto body=configured(envelope,invalid,'6');uint64_t bad_session=99,bad_result=99;
    assert(noctium_session_begin(reinterpret_cast<const uint8_t*>(body.data()),body.size(),&bad_session,&bad_result)==std::get<2>(change));assert(bad_session==0&&bad_result==0);
  }
  const auto first = start_session(with('a'));
  stage(first, "claims_evil/used", NOCTIUM_INVALID_RESPONSE);
  stage(first, "claims/used"); stage(first, "claims/other", NOCTIUM_LIMIT);
  const auto request = host_advance(first); assert(host_advance(first) == request);
  read_response(first, "\"255\"", NOCTIUM_INVALID_RESPONSE, "wrong.v1");
  read_response(first, "\"255\"", NOCTIUM_INVALID_RESPONSE, "private_state.read.v1", "other");
  read_response(first, "\"255\"", NOCTIUM_INVALID_RESPONSE, "private_state.read.v1", "store", "Bool");
  read_response(first, "\"255\"", NOCTIUM_INVALID_RESPONSE, "private_state.read.v1", "store", "UIntRange<256>", 9);
  read_response(first, "\"0255\"", NOCTIUM_INVALID_RESPONSE);
  read_response(first, "\"256\"", NOCTIUM_INVALID_RESPONSE);
  assert(host_advance(first) == request);
  read_response(first, "\"255\""); read_response(first, "\"255\"", NOCTIUM_INVALID_STATE);
  host_advance(first); resume(first, 2, "\"255\"", NOCTIUM_OK); host_advance(first);
  const auto pending = accepted(first, 'a', 'b'); assert(notice(first, 'a', 'b', "accepted") == pending);
  notice(first, 'a', 'c', "accepted", NOCTIUM_INVALID_STATE);
  commit_response(first, "committed", "r1", NOCTIUM_INVALID_RESPONSE, "wrong");
  commit_response(first, "committed", "r0", NOCTIUM_INVALID_RESPONSE);
  const auto concurrent = prepared(with('c')); accepted(concurrent, 'c', 'd');
  HostStore store; assert(store.applies == 0);
  const auto reply=store.reply(first,'a','b');
  host_call(concurrent,reply,noctium_session_resume,NOCTIUM_INVALID_RESPONSE);
  auto wrong_digest=reply;const auto digest_marker=field(reply,"journalDigest");wrong_digest.replace(wrong_digest.find(digest_marker),digest_marker.size(),std::string(64,'0'));
  host_call(first,wrong_digest,noctium_session_resume,NOCTIUM_INVALID_RESPONSE);
  auto wrong_transaction=reply;wrong_transaction.replace(wrong_transaction.find(std::string(64,'b')),64,std::string(64,'c'));
  host_call(first,wrong_transaction,noctium_session_resume,NOCTIUM_INVALID_RESPONSE);
  assert(contains(host_call(first,reply,noctium_session_resume), "\"phase\":\"committed\"")); assert(store.applies == 1);
  assert(contains(notice(first, 'a', 'b', "accepted"), "\"phase\":\"committed\""));
  private_data(first, NOCTIUM_PRIVATE_JOURNAL, NOCTIUM_INVALID_STATE);
  commit_response(first, "committed", "r1", NOCTIUM_INVALID_STATE);
  assert(noctium_session_free(first) == NOCTIUM_OK);
  assert(contains(store.apply(concurrent, 'c', 'd'), "\"phase\":\"conflicted\"")); assert(store.applies == 1);
  assert(noctium_session_free(concurrent) == NOCTIUM_OK);
  const auto retry = prepared(with('a')); accepted(retry, 'a', 'b');
  assert(contains(store.apply(retry, 'a', 'b'), "\"phase\":\"committed\"")); assert(store.applies == 1);
  assert(noctium_session_free(retry) == NOCTIUM_OK);
  const auto altered=start_session(with('a'));stage(altered,"claims/used",NOCTIUM_OK,"8675310");
  host_advance(altered);read_response(altered,"\"255\"");host_advance(altered);resume(altered,2,"\"255\"",NOCTIUM_OK);host_advance(altered);accepted(altered,'a','b');
  assert(contains(store.apply(altered,'a','b'),"\"phase\":\"conflicted\""));assert(store.applies==1);assert(noctium_session_free(altered)==NOCTIUM_OK);
  const auto uncertain = prepared(with('e')); notice(uncertain, 'e', 'f', "bind");
  notice(uncertain, 'e', 'f', "persisted"); notice(uncertain, 'e', 'f', "submitted");
  assert(contains(notice(uncertain, 'e', 'f', "uncertain"), "\"hostCasAcknowledged\":false"));
  private_data(uncertain, NOCTIUM_PRIVATE_REQUEST, NOCTIUM_INVALID_STATE);
  uint64_t result = 0; assert(noctium_session_cancel(uncertain, &result) == NOCTIUM_INVALID_STATE);
  assert(contains(notice(uncertain, 'e', 'f', "rejected"), "\"phase\":\"rejected\""));
  private_data(uncertain, NOCTIUM_PRIVATE_JOURNAL, NOCTIUM_INVALID_STATE);
  assert(noctium_session_free(uncertain) == NOCTIUM_OK);
  const auto cancelled = start_session(with('1')); stage(cancelled, "claims/used");
  assert(noctium_session_cancel(cancelled, &result) == NOCTIUM_OK); checked_take(result);
  private_data(cancelled, NOCTIUM_PRIVATE_JOURNAL, NOCTIUM_INVALID_STATE);
  assert(noctium_session_free(cancelled) == NOCTIUM_OK);
  auto bad = with('2'); const auto sum = bad.find("\"expected\":\"510\""); assert(sum != std::string::npos);
  bad.replace(sum, std::string("\"expected\":\"510\"").size(), "\"expected\":\"509\"");
  const auto failed = start_session(bad); stage(failed, "claims/used"); host_advance(failed); read_response(failed, "\"255\"");
  host_advance(failed); resume(failed, 2, "\"255\"", NOCTIUM_OK);
  assert(contains(host_advance(failed), "\"status\":\"failed\""));
  private_data(failed, NOCTIUM_PRIVATE_JOURNAL, NOCTIUM_INVALID_STATE);
  assert(noctium_session_free(failed) == NOCTIUM_OK);
  assert(store.applies==1 && store.values.size()==1 && store.values.at("claims/used")==staged_value);
  // Exhausted private-buffer quota rejects without advancing lifecycle state.
  const auto limited=prepared(with('3'));notice(limited,'3','4',"bind");
  std::vector<uint64_t> tokens;
  for(unsigned i=0;i<NOCTIUM_MAX_PRIVATE_RESULTS;++i){uint64_t token=0;assert(noctium_session_private_data(limited,NOCTIUM_PRIVATE_JOURNAL,&token)==NOCTIUM_OK);tokens.push_back(token);}
  uint64_t extra=99;assert(noctium_session_private_data(limited,NOCTIUM_PRIVATE_JOURNAL,&extra)==NOCTIUM_LIMIT);assert(extra==0);
  for(auto token:tokens)assert(noctium_private_free(token)==NOCTIUM_OK);
  assert(contains(private_data(limited,NOCTIUM_PRIVATE_JOURNAL),staged_value));
  assert(noctium_session_cancel(limited,&result)==NOCTIUM_OK);checked_take(result);assert(noctium_session_free(limited)==NOCTIUM_OK);
  auto small=context;auto at=small.find("\"privateBytes\":4096");assert(at!=std::string::npos);small.replace(at,std::string("\"privateBytes\":4096").size(),"\"privateBytes\":1024");
  at=small.find("\"writes\":1");assert(at!=std::string::npos);small.replace(at,std::string("\"writes\":1").size(),"\"writes\":64");
  const auto small_session=start_session(configured(envelope,small,'5'));bool limited_bytes=false;
  for(unsigned i=0;i<64;++i){const auto key="claims/"+std::string(100,'k')+std::to_string(i);const auto body="{\"abiVersion\":1,\"operation\":\"private_state.stage.v1\",\"capability\":\"store\",\"key\":\""+key+"\",\"type\":\"Native\",\"value\":\"8675309\"}";
    uint64_t out=99;const auto code=noctium_session_stage_private(small_session,reinterpret_cast<const uint8_t*>(body.data()),body.size(),&out);
    if(code==NOCTIUM_LIMIT){assert(out==0);limited_bytes=true;break;}assert(code==NOCTIUM_OK);checked_take(out);
  }
  assert(limited_bytes);assert(noctium_session_cancel(small_session,&result)==NOCTIUM_OK);checked_take(result);assert(noctium_session_free(small_session)==NOCTIUM_OK);
  host_cas_corpus(envelope, context, std::cin);
  return 0;
}
