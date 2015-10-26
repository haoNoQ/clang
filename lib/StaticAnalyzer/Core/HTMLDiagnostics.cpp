//===--- HTMLDiagnostics.cpp - HTML Diagnostics for Paths ----*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This file defines the HTMLDiagnostics object.
//
//===----------------------------------------------------------------------===//

#include "clang/StaticAnalyzer/Core/PathDiagnosticConsumers.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Lex/Lexer.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Rewrite/Core/HTMLRewrite.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/StaticAnalyzer/Core/BugReporter/PathDiagnostic.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"

using namespace clang;
using namespace ento;

//===----------------------------------------------------------------------===//
// Boilerplate.
//===----------------------------------------------------------------------===//

namespace {

class HTMLDiagnostics : public PathDiagnosticConsumer {
  std::string Directory;
  bool createdDir, noDir;
  const Preprocessor &PP;
  // Mapping from Bug Source File(FileID) to Report Name(std::string)
  std::map<int, std::string> FileIDPathMap;
  void addToFileIDPathMap(int ID, std::string Path) {
    FileIDPathMap[ID] = Path;
  }
  std::string getFromFileIDPathMap(int ID) { return FileIDPathMap[ID]; }
  // Mapping from Bug Source File(FileID) to Report File Rewriter(Rewriter)
  std::map<FileID, Rewriter *> FileIDRewriterMap;

  std::string getNxtEventFile(const PathDiagnosticPiece &P,
                              const PathPieces &path);

  Rewriter *PrepareReportFile(FileID FID, const SourceManager &SMgr,
                              bool isMainReportFile) {

    // Create a new rewriter to generate HTML.
    if (Rewriter *R = FileIDRewriterMap[FID])
      return R;
    SmallString<128> Model, ResultPath;
    llvm::sys::path::append(Model, Directory, isMainReportFile
                                                  ? "report-%%%%%%.html"
                                                  : "helper-%%%%%%.html");
    int fd;
    llvm::sys::fs::createUniqueFile(Model.str(), fd, ResultPath);
    addToFileIDPathMap(FID.getHashValue(), ResultPath.str());
    // Create a Rewriter to write to this html
    Rewriter *R =
        new Rewriter(const_cast<SourceManager &>(SMgr), PP.getLangOpts());
    FileIDRewriterMap[FID] = R;
    return R;
  }

  void sourceCodeListing(FileID FID, Rewriter &R) {
    html::EscapeText(R, FID);
    html::AddLineNumbers(R, FID);
    html::SyntaxHighlight(R, FID, PP);
    html::HighlightMacros(R, FID, PP);
  }

  void emitHtml(FileID FID, Rewriter &R) {
    // Get the rewrite buffer.
    const RewriteBuffer *Buf = R.getRewriteBufferFor(FID);

    if (!Buf) {
      llvm::errs() << "warning: no diagnostics generated for main file.\n";
      return;
    }

    std::string ErrorMsg;
    llvm::raw_fd_ostream os1(getFromFileIDPathMap(FID.getHashValue()).c_str(),
                             ErrorMsg);
    // Emit the HTML to disk.
    for (RewriteBuffer::iterator I = Buf->begin(), E = Buf->end(); I != E; ++I)
      os1 << *I;
  }

  void addHeader(FileID FID, Rewriter &R) {
    const SourceManager &SrcMgr = R.getSourceMgr();
    const FileEntry *Entry = SrcMgr.getFileEntryForID(FID);
    html::AddHeaderFooterInternalBuiltinCSS(R, FID, Entry->getName());
  }

  void makeMainReportFile(const PathPieces &path,
                          const PathDiagnostic &D) {
    FileID MainReportFileFID =
     (*path.rbegin())->getLocation().asLocation().getExpansionLoc().getFileID();
    Rewriter &R = *FileIDRewriterMap[MainReportFileFID];
    sourceCodeListing(MainReportFileFID, R);
    addSomeMetaToMainReportFile(path, D);
    addHeader(MainReportFileFID, R);
    emitHtml(MainReportFileFID, R);
    FileIDRewriterMap.erase(FileIDRewriterMap.find(MainReportFileFID));
    FileIDPathMap.erase(FileIDPathMap.find(MainReportFileFID.getHashValue()));
  }

  void makeHelperFile(FileID FID, const PathPieces &path,
                       const PathDiagnostic &D) {
    Rewriter &R = *FileIDRewriterMap[FID];
    sourceCodeListing(FID, R);
    addHeader(FID, R);
    emitHtml(FID, R);
  }

  void addSomeMetaToMainReportFile(const PathPieces &path,
                                   const PathDiagnostic &D) {
    // Add the name of the file as an <h1> tag.
    FullSourceLoc MainReportFileFSL =
        (*path.rbegin())->getLocation().asLocation().getExpansionLoc();

    const FileID FID = MainReportFileFSL.getFileID();
    Rewriter *R = FileIDRewriterMap[FID];
    const SourceManager &SMgr = R->getSourceMgr();
    const FileEntry *MainReportEntry = SMgr.getFileEntryForID(FID);
    llvm::SmallString<0> DirName;

    if (llvm::sys::path::is_relative(MainReportEntry->getName())) {
      llvm::sys::fs::current_path(DirName);
      DirName += '/';
    }
    {
      std::string endFile =
          getFromFileIDPathMap(MainReportFileFSL.getFileID().getHashValue());
      size_t fileIndex = endFile.find_last_of("/");
      if (fileIndex != std::string::npos)
        endFile = endFile.substr(fileIndex + 1);
      std::string s;
      llvm::raw_string_ostream os(s);
      os << "<!-- REPORTHEADER -->\n"
         << "<h3>Bug Summary</h3>\n<table class=\"simpletable\">\n"
            "<tr><td class=\"rowname\">File:</td><td>"
         << html::EscapeText(DirName)
         << html::EscapeText(MainReportEntry->getName())
         << "</td></tr>\n<tr><td class=\"rowname\">Location:</td><td>"
         << "<a href=" << endFile << "#EndPath" << ">line "
         << MainReportFileFSL.getExpansionLineNumber() << ", column "
         << MainReportFileFSL.getExpansionColumnNumber()
         << "</a></td></tr>\n<tr><td class=\"rowname\">Description:</td><td>"
         << D.getVerboseDescription() << "</td></tr>\n";

      // Output any other meta data.

      for (PathDiagnostic::meta_iterator I = D.meta_begin(), E = D.meta_end();
           I != E; ++I) {
        os << "<tr><td></td><td>" << html::EscapeText(*I) << "</td></tr>\n";
      }

      os << "</table>\n<!-- REPORTSUMMARYEXTRA -->\n"
            "<h3>Annotated Source Code</h3>\n";

      R->InsertTextBefore(SMgr.getLocForStartOfFile(FID), os.str());
    }

    // Embed meta-data tags.
    {
      std::string s;
      llvm::raw_string_ostream os(s);

      StringRef BugDesc = D.getVerboseDescription();
      if (!BugDesc.empty())
        os << "\n<!-- BUGDESC " << BugDesc << " -->\n";

      StringRef BugType = D.getBugType();
      if (!BugType.empty())
        os << "\n<!-- BUGTYPE " << BugType << " -->\n";

      StringRef BugCategory = D.getCategory();
      if (!BugCategory.empty())
        os << "\n<!-- BUGCATEGORY " << BugCategory << " -->\n";

      os << "\n<!-- BUGFILE " << DirName << MainReportEntry->getName()
         << " -->\n";

      os << "\n<!-- BUGLINE " << MainReportFileFSL.getExpansionLineNumber()
         << " -->\n";

      os << "\n<!-- BUGCOLUMN " << MainReportFileFSL.getExpansionColumnNumber()
         << " -->\n";

      os << "\n<!-- BUGPATHLENGTH " << path.size() << " -->\n";

      // Mark the end of the tags.
      os << "\n<!-- BUGMETAEND -->\n";

      // Insert the text.
      R->InsertTextBefore(SMgr.getLocForStartOfFile(FID), os.str());
    }
  }

public:
  HTMLDiagnostics(const std::string& prefix, const Preprocessor &pp);

  virtual ~HTMLDiagnostics() { FlushDiagnostics(NULL); }

  virtual void FlushDiagnosticsImpl(std::vector<const PathDiagnostic *> &Diags,
                                    FilesMade *filesMade);

  virtual StringRef getName() const {
    return "HTMLDiagnostics";
  }

  unsigned ProcessMacroPiece(raw_ostream &os,
                             const PathDiagnosticMacroPiece& P,
                             unsigned num);
  void
  HandlePiece(Rewriter& R, const PathDiagnosticPiece& P, unsigned num,
              unsigned max, const std::string &prevEventFile,
              const std::string &nxtEventFile);

  void HighlightRange(Rewriter& R, FileID BugFileID, SourceRange Range,
                      const char *HighlightStart = "<span class=\"mrange\">",
                      const char *HighlightEnd = "</span>");

  void ReportDiag(const PathDiagnostic& D,
                  FilesMade *filesMade);
};

} // end anonymous namespace

HTMLDiagnostics::HTMLDiagnostics(const std::string& prefix,
                                 const Preprocessor &pp)
  : Directory(prefix), createdDir(false), noDir(false), PP(pp) {
}

void ento::createHTMLDiagnosticConsumer(AnalyzerOptions &AnalyzerOpts,
                                        PathDiagnosticConsumers &C,
                                        const std::string& prefix,
                                        const Preprocessor &PP) {
  C.push_back(new HTMLDiagnostics(prefix, PP));
}

//===----------------------------------------------------------------------===//
// Report processing.
//===----------------------------------------------------------------------===//

void HTMLDiagnostics::FlushDiagnosticsImpl(
  std::vector<const PathDiagnostic *> &Diags,
  FilesMade *filesMade) {
  for (std::vector<const PathDiagnostic *>::iterator it = Diags.begin(),
       et = Diags.end(); it != et; ++it) {
    ReportDiag(**it, filesMade);
  }
}

std::string HTMLDiagnostics::getNxtEventFile(const PathDiagnosticPiece &P,
                                             const PathPieces &path) {

  const SourceManager &SMgr =
      P.getLocation().asLocation().getExpansionLoc().getManager();
  const FileID &FID =
      P.getLocation().asLocation().getExpansionLoc().getFileID();

  FileID MainReportFileFID =
     (*path.rbegin())->getLocation().asLocation().getExpansionLoc().getFileID();
  PrepareReportFile(FID, SMgr, MainReportFileFID == FID);
  return getFromFileIDPathMap(FID.getHashValue());
}

void HTMLDiagnostics::ReportDiag(const PathDiagnostic& D,
                                 FilesMade *filesMade) {
    
  // Create the HTML directory if it is missing.
  if (!createdDir) {
    createdDir = true;
    bool existed;
    if (llvm::error_code ec =
            llvm::sys::fs::create_directories(Directory, existed)) {
      llvm::errs() << "warning: could not create directory '"
                   << Directory << "': " << ec.message() << '\n';

      noDir = true;

      return;
    }
  }

  if (noDir)
    return;

  PathPieces path = D.path.flatten(/*ShouldFlattenMacros=*/false);

  unsigned n = path.size();
  unsigned max = n;

  std::string prevEventFile;
  std::string nxtEventFile;
  FileID MainReportFileFID =
     (*path.rbegin())->getLocation().asLocation().getExpansionLoc().getFileID();
  for (PathPieces::const_reverse_iterator I = path.rbegin(), E = path.rend();
       I != E; ++I, --n) {
    // We are emitting in a reverse order
    PathPieces::const_reverse_iterator NextPieceIt = I;
    FullSourceLoc CurrFSL = (**I).getLocation().asLocation().getExpansionLoc();
    FileID FID = CurrFSL.getFileID();
    Rewriter *R =
        PrepareReportFile(FID, CurrFSL.getManager(), FID == MainReportFileFID);
    prevEventFile = std::distance(E, ++NextPieceIt)
                        ? getNxtEventFile(**(NextPieceIt), path)
                        : "";
    HandlePiece(*R, **I, n, max, prevEventFile, nxtEventFile);
    nxtEventFile = getFromFileIDPathMap(FID.getHashValue());
  }

  makeMainReportFile(path, D);
  for (std::map<FileID, Rewriter *>::iterator it = FileIDRewriterMap.begin();
       it != FileIDRewriterMap.end(); ++it)
    makeHelperFile(it->first, path, D);

  FileIDPathMap.clear();
  FileIDRewriterMap.clear();
}

void HTMLDiagnostics::HandlePiece(Rewriter& R, const PathDiagnosticPiece& P,
                                  unsigned num, unsigned max,
                                  const std::string &prevEventFile,
                                  const std::string &nxtEventFile) {
  // For now, just draw a box above the line in question, and emit the
  // warning.
  FullSourceLoc Pos = P.getLocation().asLocation().getExpansionLoc();

  if (!Pos.isValid())
    return;

  const SourceManager &SM = R.getSourceMgr();
  std::pair<FileID, unsigned> LPosInfo = SM.getDecomposedExpansionLoc(Pos);

  const llvm::MemoryBuffer *Buf = SM.getBuffer(LPosInfo.first);
  const char* FileStart = Buf->getBufferStart();

  // Compute the column number.  Rewind from the current position to the start
  // of the line.
  unsigned ColNo = SM.getColumnNumber(LPosInfo.first, LPosInfo.second);
  const char *TokInstantiationPtr =Pos.getExpansionLoc().getCharacterData();
  const char *LineStart = TokInstantiationPtr-ColNo;

  // Compute LineEnd.
  const char *LineEnd = TokInstantiationPtr;
  const char* FileEnd = Buf->getBufferEnd();
  while (*LineEnd != '\n' && LineEnd != FileEnd)
    ++LineEnd;

  // Compute the margin offset by counting tabs and non-tabs.
  unsigned PosNo = 0;
  for (const char* c = LineStart; c != TokInstantiationPtr; ++c)
    PosNo += *c == '\t' ? 8 : 1;

  // Create the html for the message.

  const char *Kind = 0;
  switch (P.getKind()) {
  case PathDiagnosticPiece::Call:
      llvm_unreachable("Calls should already be handled");
  case PathDiagnosticPiece::Event:  Kind = "Event"; break;
  case PathDiagnosticPiece::ControlFlow: Kind = "Control"; break;
    // Setting Kind to "Control" is intentional.
  case PathDiagnosticPiece::Macro: Kind = "Control"; break;
  }

  std::string sbuf;
  llvm::raw_string_ostream os(sbuf);

  os << "\n<tr><td class=\"num\"></td><td class=\"line\"><div id=\"";

  if (num == max)
    os << "EndPath";
  else
    os << "Path" << num;

  os << "\" class=\"msg";
  if (Kind)
    os << " msg" << Kind;
  os << "\" style=\"margin-left:" << PosNo << "ex";

  // Output a maximum size.
  if (!isa<PathDiagnosticMacroPiece>(P)) {
    // Get the string and determining its maximum substring.
    const std::string& Msg = P.getString();
    unsigned max_token = 0;
    unsigned cnt = 0;
    unsigned len = Msg.size();

    for (std::string::const_iterator I=Msg.begin(), E=Msg.end(); I!=E; ++I)
      switch (*I) {
      default:
        ++cnt;
        continue;
      case ' ':
      case '\t':
      case '\n':
        if (cnt > max_token) max_token = cnt;
        cnt = 0;
      }

    if (cnt > max_token)
      max_token = cnt;

    // Determine the approximate size of the message bubble in em.
    unsigned em;
    const unsigned max_line = 120;

    if (max_token >= max_line)
      em = max_token / 2;
    else {
      unsigned characters = max_line;
      unsigned lines = len / max_line;

      if (lines > 0) {
        for (; characters > max_token; --characters)
          if (len / characters > lines) {
            ++characters;
            break;
          }
      }

      em = characters / 2;
    }

    if (em < max_line/2)
      os << "; max-width:" << em << "em";
  }
  else
    os << "; max-width:100em";

  os << "\">";

  if (max > 1) {
    os << "<table class=\"msgT\"><tr><td valign=\"top\">";
    os << "<div class=\"PathIndex";
    if (Kind) os << " PathIndex" << Kind;
    os << "\">" << num << "</div>";
    size_t fileIndex = prevEventFile.find_last_of("/");
    std::string prevFile;
    if (fileIndex != std::string::npos)
      prevFile = prevEventFile.substr(fileIndex + 1);
    else
      prevFile = prevEventFile;

    if (num > 1) {
      os << "</td><td><div class=\"PathNav\"><a href=\"" << prevFile.c_str()
         << "#Path" << (num - 1) << "\" title=\"Previous event (" << (num - 1)
         << ")\">&#x2190;</a></div></td>";
    }

    os << "</td><td>";
  }
  size_t fileIndex = nxtEventFile.find_last_of("/");
  std::string nxtFile;
  if (fileIndex != std::string::npos)
    nxtFile = nxtEventFile.substr(fileIndex + 1);
  else
    nxtFile = nxtEventFile;

  if (const PathDiagnosticMacroPiece *MP =
        dyn_cast<PathDiagnosticMacroPiece>(&P)) {

    os << "Within the expansion of the macro '";

    // Get the name of the macro by relexing it.
    {
      FullSourceLoc L = MP->getLocation().asLocation().getExpansionLoc();
      assert(L.isFileID());
      StringRef BufferInfo = L.getBufferData();
      std::pair<FileID, unsigned> LocInfo = L.getDecomposedLoc();
      const char* MacroName = LocInfo.second + BufferInfo.data();
      Lexer rawLexer(SM.getLocForStartOfFile(LocInfo.first), PP.getLangOpts(),
                     BufferInfo.begin(), MacroName, BufferInfo.end());

      Token TheTok;
      rawLexer.LexFromRawLexer(TheTok);
      for (unsigned i = 0, n = TheTok.getLength(); i < n; ++i)
        os << MacroName[i];
    }

    os << "':\n";

    if (max > 1) {
      os << "</td>";
      if (num < max) {
        os << "<td><div class=\"PathNav\"><a href=\"";
        if (num == max - 1)
          os << nxtFile.c_str() << "#EndPath";
        else
          os << nxtFile.c_str() << "#Path" << (num + 1);
        os << "\" title=\"Next event (" << (num + 1)
           << ")\">&#x2192;</a></div></td>";
      }

      os << "</tr></table>";
    }

    // Within a macro piece.  Write out each event.
    ProcessMacroPiece(os, *MP, 0);
  }
  else {
    os << html::EscapeText(P.getString());

    if (max > 1) {
      os << "</td>";
      if (num < max) {
        os << "<td><div class=\"PathNav\"><a href=\"";
        if (num == max - 1)
          os << nxtFile.c_str() << "#EndPath";
        else
          os << nxtFile.c_str() << "#Path" << (num + 1);
        os << "\" title=\"Next event (" << (num + 1)
           << ")\">&#x2192;</a></div></td>";
      }
      os << "</tr></table>";
    }
  }

  os << "</div></td></tr>";

  // Insert the new html.
  unsigned DisplayPos = LineEnd - FileStart;
  SourceLocation Loc =
    SM.getLocForStartOfFile(LPosInfo.first).getLocWithOffset(DisplayPos);

  R.InsertTextBefore(Loc, os.str());

  // Now highlight the ranges.
  ArrayRef<SourceRange> Ranges = P.getRanges();
  for (ArrayRef<SourceRange>::iterator I = Ranges.begin(),
                                       E = Ranges.end(); I != E; ++I) {
    HighlightRange(R, LPosInfo.first, *I);
  }
}

static void EmitAlphaCounter(raw_ostream &os, unsigned n) {
  unsigned x = n % ('z' - 'a');
  n /= 'z' - 'a';

  if (n > 0)
    EmitAlphaCounter(os, n);

  os << char('a' + x);
}

unsigned HTMLDiagnostics::ProcessMacroPiece(raw_ostream &os,
                                            const PathDiagnosticMacroPiece& P,
                                            unsigned num) {

  for (PathPieces::const_iterator I = P.subPieces.begin(), E=P.subPieces.end();
        I!=E; ++I) {

    if (const PathDiagnosticMacroPiece *MP =
          dyn_cast<PathDiagnosticMacroPiece>(*I)) {
      num = ProcessMacroPiece(os, *MP, num);
      continue;
    }

    if (PathDiagnosticEventPiece *EP = dyn_cast<PathDiagnosticEventPiece>(*I)) {
      os << "<div class=\"msg msgEvent\" style=\"width:94%; "
            "margin-left:5px\">"
            "<table class=\"msgT\"><tr>"
            "<td valign=\"top\"><div class=\"PathIndex PathIndexEvent\">";
      EmitAlphaCounter(os, num++);
      os << "</div></td><td valign=\"top\">"
         << html::EscapeText(EP->getString())
         << "</td></tr></table></div>\n";
    }
  }

  return num;
}

void HTMLDiagnostics::HighlightRange(Rewriter& R, FileID BugFileID,
                                     SourceRange Range,
                                     const char *HighlightStart,
                                     const char *HighlightEnd) {
  SourceManager &SM = R.getSourceMgr();
  const LangOptions &LangOpts = R.getLangOpts();

  SourceLocation InstantiationStart = SM.getExpansionLoc(Range.getBegin());
  unsigned StartLineNo = SM.getExpansionLineNumber(InstantiationStart);

  SourceLocation InstantiationEnd = SM.getExpansionLoc(Range.getEnd());
  unsigned EndLineNo = SM.getExpansionLineNumber(InstantiationEnd);

  if (EndLineNo < StartLineNo)
    return;

  if (SM.getFileID(InstantiationStart) != BugFileID ||
      SM.getFileID(InstantiationEnd) != BugFileID)
    return;

  // Compute the column number of the end.
  unsigned EndColNo = SM.getExpansionColumnNumber(InstantiationEnd);
  unsigned OldEndColNo = EndColNo;

  if (EndColNo) {
    // Add in the length of the token, so that we cover multi-char tokens.
    EndColNo += Lexer::MeasureTokenLength(Range.getEnd(), SM, LangOpts)-1;
  }

  // Highlight the range.  Make the span tag the outermost tag for the
  // selected range.

  SourceLocation E =
    InstantiationEnd.getLocWithOffset(EndColNo - OldEndColNo);

  html::HighlightRange(R, InstantiationStart, E, HighlightStart, HighlightEnd);
}
