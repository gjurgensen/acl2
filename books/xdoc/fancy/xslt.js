/*
; XDOC Documentation System for ACL2
; Copyright (C) 2009-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>
*/

// xslt.js
//
// Compatbility wrapper for lack of XSLT standards in browsers.
//
// Interface:
//   renderText(String of XDOC XML markup) -> String of Plain Text
//   renderHtml(String of XDOC XML markup) -> HTML DOM Object

// Warning: Keep this in sync with *entity-strings* and
// *entitytok-as-plaintext-fal* in ../parse-xml.lisp,
// *xml-entity-stuff* in ../prepare-topic.lisp, and
// (defxdoc entities ...) in topics.lisp.
function wrapXdocFragment(str)
{
    var wrap = "<!DOCTYPE xdoc [";
    wrap += "<!ENTITY ndash \"&#8211;\">";
    wrap += "<!ENTITY mdash \"&#8212;\">";
    wrap += "<!ENTITY larr \"&#8592;\">";
    wrap += "<!ENTITY rarr \"&#8594;\">";
    wrap += "<!ENTITY harr \"&#8596;\">";
    wrap += "<!ENTITY lang \"&#9001;\">";
    wrap += "<!ENTITY rang \"&#9002;\">";
    wrap += "<!ENTITY hellip \"&#8230;\">";
    wrap += "<!ENTITY nbsp \"&#160;\">";
    wrap += "<!ENTITY lsquo \"&#8216;\">";
    wrap += "<!ENTITY rsquo \"&#8217;\">";
    wrap += "<!ENTITY ldquo \"&#8220;\">";
    wrap += "<!ENTITY rdquo \"&#8221;\">";
    wrap += "<!ENTITY and   \"&#8743;\">";
    wrap += "<!ENTITY or    \"&#8744;\">";
    wrap += "<!ENTITY not   \"&#172;\">";
    wrap += "<!ENTITY ne    \"&#8800;\">";
    wrap += "<!ENTITY le    \"&#8804;\">";
    wrap += "<!ENTITY ge    \"&#8805;\">";
    wrap += "<!ENTITY mid   \"&#8739;\">";
    wrap += "<!ENTITY times \"&#215;\">";
    wrap += "<!ENTITY Alpha \"&#913;\">";
    wrap += "<!ENTITY Beta \"&#914;\">";
    wrap += "<!ENTITY Gamma \"&#915;\">";
    wrap += "<!ENTITY Delta \"&#916;\">";
    wrap += "<!ENTITY Epsilon \"&#917;\">";
    wrap += "<!ENTITY Zeta \"&#918;\">";
    wrap += "<!ENTITY Eta \"&#919;\">";
    wrap += "<!ENTITY Theta \"&#920;\">";
    wrap += "<!ENTITY Iota \"&#921;\">";
    wrap += "<!ENTITY Kappa \"&#922;\">";
    wrap += "<!ENTITY Lambda \"&#923;\">";
    wrap += "<!ENTITY Mu \"&#924;\">";
    wrap += "<!ENTITY Nu \"&#925;\">";
    wrap += "<!ENTITY Xi \"&#926;\">";
    wrap += "<!ENTITY Omicron \"&#927;\">";
    wrap += "<!ENTITY Pi \"&#928;\">";
    wrap += "<!ENTITY Rho \"&#929;\">";
    wrap += "<!ENTITY Sigma \"&#931;\">";
    wrap += "<!ENTITY Tau \"&#932;\">";
    wrap += "<!ENTITY Upsilon \"&#933;\">";
    wrap += "<!ENTITY Phi \"&#934;\">";
    wrap += "<!ENTITY Chi \"&#935;\">";
    wrap += "<!ENTITY Psi \"&#936;\">";
    wrap += "<!ENTITY Omega \"&#937;\">";
    wrap += "<!ENTITY alpha \"&#945;\">";
    wrap += "<!ENTITY beta \"&#946;\">";
    wrap += "<!ENTITY gamma \"&#947;\">";
    wrap += "<!ENTITY delta \"&#948;\">";
    wrap += "<!ENTITY epsilon \"&#949;\">";
    wrap += "<!ENTITY zeta \"&#950;\">";
    wrap += "<!ENTITY eta \"&#951;\">";
    wrap += "<!ENTITY theta \"&#952;\">";
    wrap += "<!ENTITY iota \"&#953;\">";
    wrap += "<!ENTITY kappa \"&#954;\">";
    wrap += "<!ENTITY lambda \"&#955;\">";
    wrap += "<!ENTITY mu \"&#956;\">";
    wrap += "<!ENTITY nu \"&#957;\">";
    wrap += "<!ENTITY xi \"&#958;\">";
    wrap += "<!ENTITY omicron \"&#959;\">";
    wrap += "<!ENTITY pi \"&#960;\">";
    wrap += "<!ENTITY rho \"&#961;\">";
    wrap += "<!ENTITY sigma \"&#963;\">";
    wrap += "<!ENTITY tau \"&#964;\">";
    wrap += "<!ENTITY upsilon \"&#965;\">";
    wrap += "<!ENTITY phi \"&#966;\">";
    wrap += "<!ENTITY chi \"&#967;\">";
    wrap += "<!ENTITY psi \"&#968;\">";
    wrap += "<!ENTITY omega \"&#969;\">";
    wrap += "<!ENTITY forall \"&#8704;\">";
    wrap += "<!ENTITY exist \"&#8707;\">";
    wrap += "<!ENTITY empty \"&#8709;\">";
    wrap += "<!ENTITY isin \"&#8712;\">";
    wrap += "<!ENTITY notin \"&#8713;\">";
    wrap += "<!ENTITY prod \"&#8719;\">";
    wrap += "<!ENTITY sum \"&#8721;\">";
    wrap += "]>";
    wrap += "<root>" + str + "</root>";
    return wrap;
}

var xslt_impl = {};

// create the nodeType constants if the Node object is not defined
if (!window.Node)
{
    var Node = {
	ELEMENT_NODE                :  1,
	ATTRIBUTE_NODE              :  2,
	TEXT_NODE                   :  3,
	CDATA_SECTION_NODE          :  4,
	ENTITY_REFERENCE_NODE       :  5,
	ENTITY_NODE                 :  6,
	PROCESSING_INSTRUCTION_NODE :  7,
	COMMENT_NODE                :  8,
	DOCUMENT_NODE               :  9,
	DOCUMENT_TYPE_NODE          : 10,
	DOCUMENT_FRAGMENT_NODE      : 11,
	NOTATION_NODE               : 12
    };
}

function unfuglifyLegacyQuotes (node)
{
    switch(node.nodeType) {
	case Node.ELEMENT_NODE:
	    // Don't fix up quotes when there is code involved.
	    // Unfortunately we have to keep this in sync with render.js
	    var tag = node.tagName.toLowerCase();
	    if (tag == "pre" || tag == "tt" || tag == "code")
		return;

	    var cl = node.getAttribute("class");
	    if (cl == "v" || cl == "tt" || cl == "mathfrag" || cl == "mathblock")
		return;
	break;

	case Node.TEXT_NODE:
	    var text = node.nodeValue;
 	    // Apparently we can't use html entities here like &ldquo; or you end
	    // up with something like &amp;ldquo; in your document.  Fortunately the
	    // unicode escapes work.  Thanks stackoverflow.
  	    text = text.replace(/``/g, '\u201c')   // ldquo, smart `` quote
	               .replace(/''/g, '\u201d')   // rdquo, smart '' quote
                       .replace(/`/g,  '\u2018')   // lsquo, smart ` quote
	               .replace(/'/g,  '\u2019');  // rsquo, smart ' quote
	    node.nodeValue = text;
	break;
    }

    for(var i = 0; i < node.childNodes.length; ++i)
    {
	var child = node.childNodes[i];
	unfuglifyLegacyQuotes(child);
    }
}

function xsltInit() {

    if (window.ActiveXObject // detects IE <= version 11
        || "ActiveXObject" in window // detects IE version 11
       )
    {
	var xslt_plain = $.base64.decode(xslt_base64);

	var xsltdom = new ActiveXObject("Msxml2.DOMDocument.6.0");
	xsltdom.validateOnParse = true;
	xsltdom.async = false;
	xsltdom.loadXML(xslt_plain);
	xslt_impl["proc"] = xsltdom;

	var xmldom  = new ActiveXObject("Msxml2.DOMDocument.6.0");
	xmldom.validateOnParse = false;
	xmldom.async = false;
	xmldom.setProperty("ProhibitDTD", false);

	xslt_impl["renderText"] = function(str) {
	    xmldom.loadXML(wrapXdocFragment(str));
	    if (xmldom.parseError.errorCode != 0) {
		var myErr = xmldom.parseError;
		try {
		    console.log("IE XML Error: " + myErr.reason);
		}catch(e) {}
		return "Error: " + myErr.reason;
	    }
	    var output = xmldom.transformNode(xsltdom);
	    var str = $("<div>" + output + "</div>").text();
	    var ret = String(str)
 		       .replace(/"/g, '&quot;')
		       .replace(/'/g, '&apos;');
	    return ret;
	};

	xslt_impl["renderHtml"] = function(str) {
	    xmldom.loadXML(wrapXdocFragment(str));
	    if (xmldom.parseError.errorCode != 0) {
		var myErr = xmldom.parseError;
		try {
		    console.log("IE XML Error: " + myErr.reason);
		}catch(e) {}
		return "Error: " + myErr.reason;
	    }
	    var output = xmldom.transformNode(xsltdom);
	    // Don't try to unfuglify quotes on IE, I run into errors
	    // in code like node.childNodes.length and it just isn't worth
	    // trying to figure out.
	    // unfuglifyLegacyQuotes(output);
	    var str = $("<div>" + output + "</div>");
	    return str;
	};
    }

    else {

	// Initialize an XSLT processor for XDOC --> HTML conversion
	xslt_impl["proc"] = new XSLTProcessor();
	var xslt_plain = $.base64.decode(xslt_base64);
	var xslt_dom = $.parseXML(xslt_plain);
	xslt_impl["proc"].importStylesheet(xslt_dom);

	xslt_impl["renderText"] = function(str) {
	    var xml = $.parseXML(wrapXdocFragment(str));
	    var dom = xslt_impl["proc"].transformToFragment(xml,document);
	    var str = $(dom).text();

	    // It's not clear to me whether this is good or bad.  The
	    // basic problem is that strings like "short" strings
	    // might legitimately have quotes or apostrophes in them.
	    // This is no problem if we're going to stick the
	    // renderText into a paragraph or something like that.
	    // But it *is* a problem if we're going to stick it into
	    // an attribute like a tooltip or similar.  So, just to
	    // avoid problems like that, make sure the resulting
	    // string is free of " and ' characters.
	    return String(str)
		.replace(/"/g, '&quot;')
		.replace(/'/g, '&apos;');
	};

	xslt_impl["renderHtml"] = function(str) {
	    var xml = $.parseXML(wrapXdocFragment(str));
	    var dom = xslt_impl["proc"].transformToFragment(xml,document);
	    unfuglifyLegacyQuotes(dom);
	    return dom;
	};
    }
}

function renderText(str) {
    return xslt_impl["renderText"](str);
}

function renderHtml(str) {
    return xslt_impl["renderHtml"](str);
}

xsltInit();
