/*
blahtex: a TeX to MathML converter designed with MediaWiki in mind
blahtexml: an extension of blahtex with XML processing in mind
http://gva.noekeon.org/blahtexml

Copyright (c) 2006, David Harvey
Copyright (c) 2009, Gilles Van Assche
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
    * Neither the names of the authors nor the names of their affiliation may be used to endorse or promote products derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

#include <sstream>
#include "Interface.h"
#include "MathmlNode.h"
#include "UnicodeConverter.h"
#include "Misc.h"
#include <stdlib.h>
#include <string.h>
#include <iostream>
#include <stdexcept>

using namespace std;

namespace blahtex
{

void Interface::ProcessInput(const wstring& input, bool displayStyle)
{
    mManager.reset(new Manager);
    mManager->ProcessInput(input, mTexvcCompatibility, displayStyle);
}

wstring Interface::GetMathml()
{
    wostringstream output;
    auto_ptr<MathmlNode> root = mManager->GenerateMathml(mMathmlOptions);
    root->Print(output, mEncodingOptions, mIndented);
    return output.str();
}

wstring Interface::GetPurifiedTex()
{
    return mManager->GeneratePurifiedTex(mPurifiedTexOptions);
}

wstring Interface::GetPurifiedTexOnly()
{
    return mManager->GeneratePurifiedTexOnly();
}

#ifdef BLAHTEXML_USING_XERCES
void Interface::PrintAsSAX2(ContentHandler& sax, const wstring& prefix, bool ignoreFirstmrow) const
{
    wostringstream output;
    auto_ptr<MathmlNode> root = mManager->GenerateMathml(mMathmlOptions);
    root->PrintAsSAX2(sax, prefix, ignoreFirstmrow);
}
#endif

}

// Imported from Messages.cpp:
extern wstring GetErrorMessage(const blahtex::Exception& e);
extern wstring GetErrorMessages();

using namespace blahtex;
// this is the equivalent of
//   blahtex --mathml --mathml-encoding long --disallow-plane-1 --indented --spacing relaxed
extern "C" char *texToMathML(char *inputUtf8) {
  blahtex::Interface interface;
  // --disallow-plane-1
  interface.mMathmlOptions.mAllowPlane1 = false;
  interface.mEncodingOptions.mAllowPlane1 = false;
  // --indented
  interface.mIndented = true;
  // --mathml-encoding long
  interface.mEncodingOptions.mMathmlEncoding = EncodingOptions::cMathmlEncodingLong;
  // --spacing relaxed
  interface.mMathmlOptions.mSpacingControl = MathmlOptions::cSpacingControlRelaxed;
  // --mathml
  UnicodeConverter gUnicodeConverter;
  gUnicodeConverter.Open();
  wstring input = gUnicodeConverter.ConvertIn(inputUtf8);
  string outputUtf8;
  try {
    interface.ProcessInput(input, false);
    wostringstream mathmlOutput;
    // could simplify this output but then it would not be compatible
    // with the commandline tool anymore
    mathmlOutput << L"<blahtex>\n" << L"<mathml>\n" << L"<markup>\n";
    mathmlOutput << interface.GetMathml();
    if (!interface.mIndented)
      mathmlOutput << L"\n";
    mathmlOutput << L"</markup>\n" << L"</mathml>\n" << L"</blahtex>\n";
    outputUtf8 = gUnicodeConverter.ConvertOut(mathmlOutput.str());
  }
  catch (blahtex::Exception& e) {
    outputUtf8 = "error (" + gUnicodeConverter.ConvertOut(e.GetCode()) + ") " + gUnicodeConverter.ConvertOut(GetErrorMessage(e));
  }
  // The following errors might occur if there's a bug in blahtex that
  // some assertion condition picked up. We still want to report these
  // nicely to the user so that they can notify the developers.
  catch (std::logic_error& e) {
    outputUtf8 = "error (logic_error)";
    outputUtf8 += e.what();
  }
  // These kind of errors should only occur if the program has been
  // installed incorrectly.
  catch (std::runtime_error& e) {
    outputUtf8 = "error (runtime_error)";
    outputUtf8 += e.what();
  }
  int len = outputUtf8.length();
  char *result = (char*)malloc(len+1);
  memcpy(result, outputUtf8.c_str(), len);
  result[len] = 0;
  return result;
}

// end of file @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@
