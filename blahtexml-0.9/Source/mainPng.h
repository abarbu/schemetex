/*
blahtex: a TeX to MathML converter designed with MediaWiki in mind
blahtexml: an extension of blahtex with XML processing in mind
http://gva.noekeon.org/blahtexml

Copyright (c) 2006, David Harvey
Copyright (c) 2010, Gilles Van Assche
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
    * Neither the names of the authors nor the names of their affiliation may be used to endorse or promote products derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

#ifndef BLAHTEX_MAINPNG_H
#define BLAHTEX_MAINPNG_H

#include <string>

// Records information about a PNG file generated by MakePngFile.
struct PngInfo
{
    // The PNG is stored in md5.png.
    std::string mMd5;
    std::string fullFileName;

    // These are the height and depth reported by dvipng.
    // They are only valid if mDimensionsValid is set.
    bool mDimensionsValid;
    int mHeight;
    int mDepth;
    
    PngInfo() :
        mDimensionsValid(false)
    { }
};

struct PngParams
{
    std::string tempDirectory;
    std::string pngDirectory;
    std::string shellLatex;
    std::string shellDvipng;
    bool deleteTempFiles;
};

// Generates a PNG file. Uses tempDirectory for storage of temporary files
// (.tex, .dvi, .log, .data). Expects tempDirectory and pngDirectory to
// include a terminating slash. The output file will be stored in the
// directory pngDirectory in the file pngFilename; if pngFilename is an
// empty string, MakePngFile will just use the md5 that it computes (which
// gets returned in PngInfo).
extern PngInfo MakePngFile(
    const std::wstring& purifiedTex,
    const std::string& pngFilename,
    const PngParams& params
);


#endif

// end of file @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@
