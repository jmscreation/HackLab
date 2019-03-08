/*
 * Encode.JS - A powerful data manipulation library
 * Supports many encryption standards plus other useful features
 * Version 2.2.3
 * 
 * Support List:
 *  fstream:		Read and write to a block of bytes.
 *  bitstream:		Read and write to a block of data in bits as opposed to bytes.
 *  unicode:		Convert JS strings between unicode formats.
 *  base64:			Convert to and from the base-64 standard, or choose a custom alphabet.
 *  hex:			Convert to and from hexadecimal.
 *  binary:			Convert to and from binary.
 *  ascii85:		Convert to and from the ascii85 standard, or choose a custom alphabet.
 *  crc:			Calculate the CRC of a block of data with any polynomial.
 *  dword:			Read or generate 4-byte dwords in big or little endian.
 *  rle:			Compress data with run-length encoding.
 *  lzw:			Compress data with the Lempel-Ziv Welch (LZW) compression standard.
 *  rc4:			Cipher data with the RC4 encryption standard.
 *  codepack:		Pack code or plain-text with a simple string packer.
 *  md5:			Calculate the standard MD5 hash on data.
 *  sha1:			Calculate the standard SHA1 hash on data.
 *  sha2:			Calculate the standard SHA2 hash on data; supports all four standard block sizes: 224, 256, 384, and 512 bits
 *  buffermath:		Run math to combine or process buffers of data.
 *  bcmode:			Set up a block-cipher mode of operation for any of the block-ciphers.
 *  aes:			Encrypt and decrypt data with the Advanced Encryption Standard (AES), using block sizes of 128, 192, or 256 bits.
 *  idea:			Encrypt and decrypt data with the International Data Encryption Algorithm (IDEA) standard.
 *  salsa20:		Hash data, or generate a data stream for encryption, using the salsa20 encryption standard.
 *  des:			Encrypt and decrypt data using the Data Encryption Standard, or switch to TripleDES.
 */

var encode = new (function(w,undef){'use strict';var t=this;
	function strrep(s,n) {n=n||0;return Array(n+1).join(s)}
	function bitrot(x,b) {return (((x<<b)>>>0)|(x>>>32-b))>>>0}
	var chr=String.fromCharCode,cca="charCodeAt";
	
	t.fstream = function(str){var tt=this; if(!(tt instanceof t.fstream)) throw "Bad Instantiation of encode.fstream";
		str=str||"";
		var rpos=0,wpos=0;
		function write(s) {
			if(wpos==str.length) {str+=s; return} // append
			var bef=str.slice(0,wpos),aft=wpos+s.length>str.length?"":str.slice(wpos+s.length);
			str=bef+s+aft;
			wpos+=s.length;
		}
		tt.write = {
			chr:function(c){var o=""; if(+c===c) o+=chr(c); else if(""+c===c) o+=c[0]; write(o)},
			integer:function(n, b){var o=""; b=+b===b?b:4; for(var i=0;i<b;i++) {o+=chr(n&255); n>>=8}; write(o)},
			decimal:function(n, w,f){var o=""; w=+w===w?w:2; f=+f===f?f:2; for(var i=f;i>-w;i--) o+=chr(n*Math.pow(256,i)&255); write(o)},
			string:function(s, lb){var o=""; lb=+lb===lb?lb:2; tt.write.integer(s.length,2); o+=s; write(o)},
			binary:function(s){write(s)},
			seek:function(pos){wpos=pos<0||pos>str.length?str.length:pos},
			tell:function(){return wpos}
		};
		tt.read = {
			chr:function(){return str.charCodeAt(rpos++)},
			integer:function(b,sn){b=+b===b?b:4; for(var n=0,f=1,i=0;i<b;i++) {n+=str.charCodeAt(rpos++)*f; f<<=8}; if(sn && (str.charCodeAt(rpos-1)&128)) n|=(-1^(f-1)); return n},
			decimal:function(w,f,sn){w=+w===w?w:2; f=+f===f?f:2; for(var n=0,i=f;i>-w;i--) n+=str.charCodeAt(rpos++)*Math.pow(256,-i); if(sn && (str.charCodeAt(rpos-1)&128)) n=-n-Math.pow(256,-f); return n},
			string:function(lb){lb=+lb===lb?lb:2; var l=tt.read.integer(2), s=str.slice(rpos,rpos+l); rpos+=l; return s},
			binary:function(n){var s=str.slice(rpos,rpos+n); rpos+=n; return s},
			eof:function(){return rpos>=str.length},
			seek:function(pos){rpos=pos<0||pos>str.length?str.length:pos},
			tell:function(){return rpos}
		};
		tt.string = function(v){if(""+v===v) str=v; return str}
	}
	
	t.bitstream = function(data,cr,br,cw,bw){var tt=this; if(!(tt instanceof t.bitstream)) throw "Bad Instantiation of encode.bitstream";
		// cr: read character position, br: bits in read buffer, cw: write character position, bw: bits in write buffer
		if(typeof data != "string") data="";
		if(+cr!==cr) cr=0; if(+br!==br) br=0;
		if(+cw!==cw) cw=0; if(+bw!==bw) bw=0;
		cr+=Math.floor(br/8); br%=8;
		cw+=Math.floor(bw/8); bw%=8;
		var wbuf=0,wbeg=bw,rbuf=0,rbeg=br; br=0;
		
		tt.read = function(bits) {
			if(+bits!==bits || bits<0) bits=0;
			var er=false;
			
			while(br<bits) {
				if(cr<0) er=true;
				else rbuf |= (rbeg? ((data[cr]||0)>>rbeg) : ((data[cr]||0)<<br) );
				cr++; br+=8-rbeg; rbeg=0;
			}
			if(er) throw "Bad read location for encode.bitstream.read. Cannot read negative locations.";
			
			var v=(rbuf & ((1<<bits)-1));
			rbuf>>=bits; br-=bits;
			return v;
		}
		tt.readfinish = function() {
			if(rbeg) {rbuf|=(data[cr]>>rbeg); br=8-rbeg; rbeg=0}
			if(br==0) return 0;
			var v=rbuf;
			cr++; rbuf=0; br=0;
			return v;
		}
		tt.tellr = function(mode) {
			var bts=cr*8-br+rbeg;
			if(mode===1) return bts%8;
			if(mode===2) return bts;
			return Math.floor(bts/8);
		}
		tt.seekr = function(chr,bit,from) {
			if(+from!==from) from=0;
			var bts=(+chr===chr&&chr*8)+(+bit===bit&&bit);
			if(from==1) bts+=cr*8-br+rbeg;
			if(from==2) bts=data.length*8-bts;
			cr=Math.floor(bts/8); rbeg=bts%8;
			rbuf=0; br=0;
		}
		tt.write = function(buffer,bits) {
			if(+bits!==bits || bits<0) bits=0;
			if(!bits) return;
			
			wbuf |= ((buffer&((1<<bits)-1)) << bw);
			bw+=bits;
			var er=false;
			while(rbeg+bw>=8) {
				if(cw<0) er=true;
				else data[cw]=(wbeg ? ((data[cw] & (1<<wbeg)-1) | ((wbuf<<wbeg)&255)) : (wbuf&255));
				cw++; wbuf>>=8-wbeg; bw-=8-wbeg; wbeg=0;
			}
			if(er) throw "Bad write location for encode.bitstream.write. Cannot write to negative locations.";
		}
		tt.writefinish = function(padding,bits) {
			if(bw==0) {wbuf=0; return}
			if(+padding===padding) {
				if(+bits!==bits || bits<0) bits=8;
				wbuf |= ((padding&(1<<bits)-1) << bw);
				var bt=data[cw]||0;
				bt &= (1<<wbeg)-1;
				data[cw++]=(bt|((wbuf<<wbeg)&255));
				wbuf=0; bw=0; wbeg=0;
			} else {
				var bt=data[cw]||0;
				bt &= ~((1<<bw)-1<<wbeg);
				bt |= wbuf<<wbeg;
				data[cw]=bt&255;
				wbuf=0; bw+=wbeg; cw+=Math.floor(bw/8); wbeg=bw%8; bw=0;
			}
		}
		tt.tellw = function(mode) {
			var bts=cw*8+bw+wbeg;
			if(mode===1) return bts%8;
			if(mode===2) return bts;
			return Math.floor(bts/8);
		}
		tt.seekw = function(chr,bit,from){
			if(+from!==from) from=0;
			var bts=(+chr===chr&&chr*8)+(+bit===bit&&bit);
			if(from==1) bts+=cw*8+bw;
			if(from==2) bts=data.length*8-bts;
			tt.writefinish();
			cw=Math.floor(bts/8); bw=0;
			wbeg=bts%8; wbuf=0;
		}
		tt.clear = function() {
			data=[]; wbuf=rbuf=wbeg=cw=bw=cr=br=0;
		}
		tt.setdata = function(dat,append) {
			if(!append) {data=[]; rbuf=0; rbeg=br; br=0; wbuf=0; wbeg=bw; bw=0}
			for(var i=0;i<dat.length;i++) data.push(dat[cca](i)&0xFF);
		}
		tt.getdata = function() {
			var dat="";
			for(var i=0;i<data.length;i++) dat+=chr(data[i]);
			return dat;
		}
		
		tt.setdata(data);
	}
	
	var unitys={uni16:0,unibe16:1,utf8:2,utf32:3,utfbe32:4};
	t.unicode = function(defcode) {var tt=this; if(!(tt instanceof t.unicode)) throw "Bad Instantiation of encode.unicode";
		if(typeof defcode=="string") defcode=(unitys[defcode])||2;
		function _uni16(c) {return chr(c&0xFF)+chr((c>>8)&0xFF)}
		function _unibe16(c) {return chr((c>>16)&0xFF)+chr(c&0xFF)}
		function _utf8(c) {var i,b=(Math.log2(c)|0)+1,B=b>7?((b-2)/5|0):0,o="";
			o+=chr((B?(0xFF<<7-B)&0xFF:0)|((c>>B*6)&(0xFF>>B+!!B+1)));
			for(i=B-1;i>=0;i--) o+=chr(0x80|((c>>i*6)&0x3F)); return o;
		}
		function _uni32(c) {return chr(c&255)+chr((c>>8)&255)+chr((c>>16)&255)+chr((c>>24)&255)}
		function _unibe32(c) {return chr((c>>24)&255)+chr((c>>16)&255)+chr((c>>8)&255)+chr(c&255)}
		function uni16_(o) {return chr(o.s[cca](o.i++)+o.s[cca](o.i++)*256)}
		function unibe16_(o) {return chr(o.s[cca](o.i++)*256+o.s[cca](o.i++))}
		function utf8_(o) {var cf=o.s[cca](o.i++),c,b=0x40,i=0,v=0;
			if(cf&0x80) while(cf&b) {c=o.s[cca](o.i++); b>>=1; i++;
				if((c&0xC0)^0x80) throw "Unicode Error: Unexpected UTF-8 Code-Point Interruption @"+(o.i-1);
				if(b==1) throw "Unicode Error: Code-Point Value Beyond Range of UTF-8 Standard @"+(o.i-1);
				v=(v<<6)|(c^0x80);
			} else b<<=1;
			v|=(cf&b-1)<<i*6;
			return chr(v);
		}
		function uni32_(o) {return chr(o.s[cca](o.i++)+(o.s[cca](o.i++)<<8)+(o.s[cca](o.i++)<<16)+(o.s[cca](o.i++)<<24))}
		function unibe32_(o) {return chr((o.s[cca](o.i++)<<24)+(o.s[cca](o.i++)<<16)+(o.s[cca](o.i++)<<8)+o.s[cca](o.i++))}
		
		tt.to = function(str,code) {
			if(typeof code=="string") code=unitys[code];
			else if(+code!==code) code=defcode; code=code|0;
			if(code<0 || code>4) code=defcode;
			code = [_uni16,_unibe16,_utf8,_uni32,_unibe32][code];
			for(var i=0,o="",c;i<str.length;i++)
				o+=code(str[cca](i));
			return o;
		}
		tt.from = function(str,code) {
			if(typeof code=="string") code=unitys[code];
			else if(+code!==code) code=defcode; code=code|0;
			if(code<0 || code>4) code=defcode;
			if((code==0 || code==1) && str.length%2) throw "Unicode Error: Invalid Unicode String for "+(code==1?"unibe16":"uni16")+" Conversion: Uneven Length";
			if((code==3 || code==4) && str.length%4) throw "Unicode Error: Invalid Unicode String for "+(code==4?"unibe32":"uni32")+" Conversion: Length Not Multiple of 4"
			code = [uni16_,unibe16_,utf8_,uni32_,unibe32_][code];
			var ctr={i:0,s:str},o="";
			while(ctr.i<str.length)
				o+=code(ctr);
			return o;
		}
	}
	var uni=new t.unicode();
	t.unicode.to=uni.to; t.unicode.from=uni.from;
	
	t.base64 = function(al){var tt=this; if(!(tt instanceof t.base64)) throw "Bad Instantiation of encode.base64";
		var usenew=(""+al===al&&al.length==64),B64=usenew?al:"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/",_al;
		if(usenew||!w.btoa||!w.atob) {_al={}; for(var i=0;i<B64.length;i++) _al[B64[i]]=i}
		tt.to= (!usenew&&function(){return w.btoa.apply(null,arguments)})||function(data) {
			var s="",i=0,b=0,c=0,l=data.length;
			while(i<l) {b<6&&(c=((c<<8)|(data[cca](i++))),b+=8);b-=6;s+=B64[c>>b];c&=(1<<b)-1}
			b>0&&(s+=B64[c<<6-b]+strrep("=",3-b/2));return s;
		}
		tt.from= (!usenew&&function(){return w.atob.apply(null,arguments)})||function(data) {
			var i=0,c,x=0,b=0,l=s.length,data="";
			while(i<l) {c=_al[s[i++]];if(c===undef) throw "Invalid Character '"+s[i-1]+"'. Could not complete base64 decode.";
				b+=6;x=((x<<6)|c);if(b<8) continue;data+=chr(x>>b-8);x&=(1<<b-8)-1;b-=8}
			return data;
		}
	}
	var b64 = new t.base64();
	t.base64.to=b64.to; t.base64.from=b64.from;
	
	t.hex = function(defcaps){var tt=this; if(!(tt instanceof t.hex)) throw "Bad Instantiation of encode.hex";
		tt.to = function(data,caps) {
			caps=(caps===undef)?!!defcaps:!!caps;
			for(var i=0,s="",c;i<data.length;i++) {
				c=data[cca](i);
				s+=(c<16?"0":"")+c.toString(16);
			}
			return caps?s.toUpperCase():s;
		}
		tt.from = function(data) {if(data.length%2) throw "Invalid Length. Must be even (in hex character-pairs). Could not complete hex decode.";
			for(var i=0,s="",c;i<data.length;i+=2) {c = +("0x"+data.slice(i,i+2));
				if(isNaN(c))throw "Invalid Hex Pair '"+data.slice(i,i+2)+"'. Could not complete hex decode.";
				s+=chr(c);
			}
			return s;
		}
	}
	var hex = new t.hex();
	t.hex.to=hex.to; t.hex.from=hex.from;
	
	var lsbtable=new Array(256), msbtable=new Array(256);
	t.binary = function(defmsb){var tt=this; if(!(tt instanceof t.binary)) throw "Bad Instantiation of encode.binary";
		tt.to = function(data,msb) {
			msb=(msb===undef)?!!defmsb:!!msb;
			var tbl=msb?msbtable:lsbtable;
			for(var i=0,s="",c,j,b,B,bt;i<data.length;i++) {
				b=msb?128:1; B=data[cca](i);
				if(!(bt=tbl[B])) {
					for(bt="",j=0;j<8;j++) {bt+=(B&b)?"1":"0"; msb?(b>>=1):(b<<=1)}
					tbl[B]=bt;
				}
				s+=bt;
			}
			return s;
		}
		tt.from = function(data,msb) {
			msb=(msb===undef)?!!defmsb:!!msb;
			if(data.length%8) throw "Invalid Length. Must be divisible by 8. Could not complete binary decode.";
			for(var i=0,s="",j,b,B;i<data.length;i+=8) {
				b=msb?128:1; B=0;
				for(j=0;j<8;j++) {B|=(data[i+j]=="1"?b:0); msb?(b>>=1):(b<<=1)}
				s+=chr(B);
			}
			return s;
		}
	}
	var bin = new t.binary();
	t.binary.to=bin.to; t.binary.from = bin.from;
	
	t.ascii85 = function(al,defusewrap){var tt=this; if(!(tt instanceof t.ascii85)) throw "Bad Instantiation of encode.ascii85";
		var A85=(""+al===al&&al.length==85)?al:"!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstu";
		var _al={}; for(var i=0;i<A85.length;i++) _al[A85[i]]=i;
		if(defusewrap===undef) defusewrap=true;
		if(A85.indexOf("<")>-1 || A85.indexOf(">") || A85.indexOf("~")>-1) defusewrap=-1;
		tt.to = function(data,usewrap) {
			if(defusewrap===-1) usewrap=false;
			else if(usewrap===undef) usewrap=defusewrap; else usewrap=!!usewrap;
			var s=usewrap?"<~":"",b=0,c,i,j,l=data.length;
			if(l%4!=0) b=4-l%4;
			for(i=0;i<l;i+=4) {
				c=data[cca](i)*16777216+(i+1<l?data[cca](i+1)*65536:0)+(i+2<l?data[cca](i+2)*256:0)+(i+3<l?data[cca](i+3):0);
				for(j=0;j<5-b*(i+4>l);j++)
					s+=A85[Math.floor(c/(1+(j<4)*84)/(1+(j<3)*84)/(1+(j<2)*84)/(1+(j<1)*84))%85];
			}
			if(usewrap) s+="~>";
			return s;
		}
		tt.from = function(data) {
			var x,excess=0,i,j,L,p0,p1,p2,p3,p4,pc,s="";
			if(defusewrap!==-1 && data.slice(0,2)=="<~" && data.slice(-2)=="~>") data=data.slice(2,-2);
			
			if(data.length%5>0) {excess=5-data.length%5; data+=strrep(A85[A85.length-1],excess)}
			for(var i=0,l=data.length;i<l;i+=5) {
				p0=_al[data[i]];p1=_al[data[i+1]];p2=_al[data[i+2]];p3=_al[data[i+3]];p4=_al[data[i+4]];
				if((p0===undef&&(pc=data[i]))||(p1===undef&&(pc=data[i+1]))||(p2===undef&&(pc=data[i+2]))||(p3===undef&&(pc=data[i+3]))||(p4===undef&&(pc=data[i+4])))
					throw "Invalid Character '"+pc+"'. Could not complete ASCII85 decode.";
				x=p0*52200625+p1*614125+p2*7225+p3*85+p4;
				for(j=0,L=4-excess*(i+5 == data.length);j<L;j++) s+=chr((x>>>24-j*8)&255);
			}
			return s;
		}
	}
	var a85 = new t.ascii85();
	t.ascii85.to=a85.to; t.ascii85.from=a85.from;
	
	t.crc = function(crcpoly,definvbef,definvaft){var tt=this; if(!(tt instanceof t.crc)) throw "Bad Instantiation of encode.crc";
		var crctable=[];crcpoly=(typeof crcpoly=="number")?(crcpoly>>>0):0xEDB88320;
		definvbef=!!definvbef; definvaft=!!definvaft;
		(function(){
			for(var i=0,j,c;i<256;i++) {
				c=(i>>>0);
				for(j=0;j<8;j++)
					if(c&1) c=((crcpoly^(c>>>1))>>>0);
					else c=(c>>>1);
				crctable[i]=c;
			}
		})();
		tt.hash = function(data,invbef,invaft) {
			if(invbef===undef) invbef=definvbef; else invbef=!!invbef;
			if(invaft===undef) invaft=definvaft; else invaft=!!invaft;
			var c=invbef?0xFFFFFFFF:0;
			for(var i=0;i<data.length;i++)
				c=((crctable[(c^(data[cca](i)&0xFF))&255]^(c>>>8))>>>0);
			return invaft?((c^0xFFFFFFFF)>>>0):(c>>>0);
		}
	}
	var crc = new t.crc();
	t.crc.hash=crc.hash;
	
	t.dword = function(MSB,signed){var tt=this; if(!(tt instanceof t.dword)) throw "Bad Instantiation of encode.dword";
		MSB=!!MSB; signed=!!signed;
		tt.to = MSB ? function(x) {return chr((x>>>24)&255)+chr((x>>>16)&255)+chr((x>>>8)&255)+chr(x&255)}
				   : function(x) {return chr(x&255)+chr((x>>>8)&255)+chr((x>>>16)&255)+chr((x>>>24)&255)};
		tt.from = MSB ? (signed ? function(dw) {var c=dw[cca](0)&255,v=c*16777216+(dw[cca](1)&255)*65536+(dw[cca](2)&255)*256+(dw[cca](3)&255);return (c&128)?-~v-1:v}
							   : function(dw) {return (dw[cca](0)&255)*16777216+(dw[cca](1)&255)*65536+(dw[cca](2)&255)*256+(dw[cca](3)&255)})
					 : (signed ? function(dw) {var c=dw[cca](3)&255,v=(dw[cca](0)&255)+(dw[cca](1)&255)*256+(dw[cca](2)&255)*65536+c*16777216;return (c&128)?-~v-1:v}
							   : function(dw) {return (dw[cca](0)&255)+(dw[cca](1)&255)*256+(dw[cca](2)&255)*65536+(dw[cca](3)&255)*16777216});
	}
	var dwd = new t.dword(),dwdbe = new t.dword(true);
	t.dword.to=dwd.to; t.dword.from=dwd.from; t.dword.be = {to:dwdbe.to,from:dwdbe.from};
	
	t.rle = function(){var tt=this; if(!(tt instanceof t.rle)) throw "Bad Instantiation of encode.rle";
		tt.to = function(data) {
			for(var s="",rle=0,pc=-1,c,cnt=0,i=0;i<data.length;i++) {c=data[cca](i);
				if(rle && (c!=pc || ++cnt==255)) {s+=chr(cnt); pc=-1; rle=0; if(cnt==255) {cnt=0; continue}; cnt=0}
				if(!rle) {rle=(c==pc); s+=data[i]; pc=c}
			}
			if(rle) s+=chr(cnt);
			return s;
		}
		tt.from = function(data) {
			for(var s="",pc=-1,c,i=0;i<data.length;i++) {s+=(c=data[i]);
				if(pc==c) {c=data[cca](++i); s+=strrep(pc,c); c=""}
				pc=c;
			}
			return s;
		}
	}
	var rle = new t.rle();
	t.rle.to=rle.to; t.rle.from=rle.from;
	
	// dependents: bitstream
	var defd=[],log2=Math.log(2); for(var i=0;i<256;i++) defd.push(chr(i));
	t.lzw = function(maxbits,al){var tt=this; if(!(tt instanceof t.lzw)) throw "Bad Instantiation of encode.lzw";
		var defdict=defd,defd_l=256; if(""+al===al) {defd_l=al.length; defdict=al.split("")}
		var minbits=Math.ceil(Math.log(defdict.length)/log2);
		if(+maxbits!==maxbits || maxbits<minbits) maxbits=minbits+1;
		
		var mx = (1<<maxbits);
		function search(dict,wd) {
			for(var e,el,big=null,i=0,l=dict.length;i<l;i++) {
				e=dict[i];el=e.length;
				if((!big || el>big.l) && (e == wd.slice(0,el)))
					big={l:el,i:i};
			}
			if(big === null) throw "Internal Error in encode.lzw.search: No compatible dictionary entry was found for the word: '"+wd+"'.";
			return big;
		}
		function addentry(dict,wd) {
			dict.push(wd);
		}
		function popdict(dict,fall) {
			if(dict.length>=mx-fall) dict.splice(defd_l,1);
		}
		function promote(dict,ind) {
			if(ind<defd_l) return;
			dict.push(dict.splice(ind,1)[0]);
		}
		tt.to = function(data) {
			var dict=defdict.slice(),wd,ind,dlen=1,bits=minbits;
			var stream = new t.bitstream();
			var i=0,l=data.length;
			
			while(i<l) {
				wd=data.slice(i,i+dlen);
				ind=search(dict,wd);				// read word from message
				stream.write(ind.i,bits);			// WRITE WORD
				promote(dict,ind.i);				// promote word entry
				addentry(dict,data.slice(i,i+ind.l+1)); // add new entry
				popdict(dict,0);						// drop oldest entry
				dlen=(dlen<ind.l+1)?ind.l+1:dlen;
				if(dict.length-1>>bits) bits++;		// re-evaluate bits
				i+=ind.l;
			}
			stream.writefinish();
			return stream.getdata();
		}
		tt.from = function(data) {
			var dict=defdict.slice(),pwd="",wd,ind,bits=minbits;
			var stream = new t.bitstream(data);
			var s="";
			
			while(stream.tellr(2)<data.length*8-7) {
				ind=stream.read(bits);
				if(ind==dict.length) wd=pwd+pwd[0]; else wd=dict[ind]; // READ WORD
				s+=wd;								// write word to output
				if(pwd) addentry(dict,pwd+wd[0]);	// add new entry (the encoder's previous entry at this time)
				promote(dict,ind);					// promote word entry
				if(pwd) popdict(dict,1);			// drop oldest entry
				if(dict.length>>bits) bits++;		// re-evaluate bits
				pwd=wd;
			}
			return s;
		}
	}
	var lzw = new t.lzw();
	t.lzw.to=lzw.to; t.lzw.from=lzw.from;
	
	var deftable=[]; for(var i=0;i<256;i++) deftable[i]=i;
	t.rc4 = function(defkey) {var tt=this; if(!(tt instanceof t.rc4)) throw "Bad Instantiation of encode.rc4";
		if(typeof defkey == "string") defkey=defkey.slice(0,256); else defkey=chr(0);
		var table=null;
		
		function gentable(key) {
			var tbl = deftable.slice(),i,j=0,l=key.length,_;
			for(i=0;i<256;i++) {
				j=((j+tbl[i]+key[cca](i%l)) & 255);
				_=tbl[i]; tbl[i]=tbl[j]; tbl[j]=_;
			}
			return tbl;
		}
		function cleartable(tbl) {
			for(var i=0;i<tbl.length;i++)
				tbl[i]=0;
		}
		tt.to = tt.from = tt.cipher = function(data,key) {
			var tbl;
			if(typeof key == "string" && key.length>0) tbl=gentable(key);
			else tbl=(table||(table=gentable(defkey))).slice();
			
			var len=data.length,out="";
			var i=0,j=0,k=0,_;
			while(k<len) {
				i=((i+1)&255); j=((j+tbl[i])&255);
				_=tbl[i]; tbl[i]=tbl[j]; tbl[j]=_;
				out += chr(data[cca](k++) ^ tbl[(tbl[i]+_)&255]);
			}
			cleartable(tbl);
			return out;
		}
		tt.stream = function(length,key) {
			var tbl;
			if(typeof key == "string") tbl=gentable(key);
			else tbl=(table||(table=gentable(defkey))).slice();
			
			var i=0,j=0,k=0,_,out="";
			while(k++<length) {
				i=(i+1&255); j=(j+tbl[i]&255);
				_=tbl[i]; tbl[i]=tbl[j]; tbl[j]=_;
				out += chr(tbl[tbl[i]+_&255]);
			}
			cleartable(tbl);
			return out;
		}
		tt.flush = function() {
			cleartable(table);
			table=null;
		}
	}
	var rc = new t.rc4();
	t.rc4.cipher=rc.cipher; t.rc4.stream=rc.stream; t.rc4.flush=rc.flush;
	
	var pakal="0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ_abcdefghijklmnopqrstuvwxyz";
	t.codepack = function(defsep) {var tt=this; if(!(tt instanceof t.codepack)) throw "Bad Instantiation of encode.codepack";
		defsep=!!defsep;
		tt.to = function(str,sep) {
			function nextwd(){var i=ind++,s="";while(i>0){s+=pakal[i%pakal.length];i=Math.floor(i/pakal.length)};if(s=="")s=pakal[0];return s}
			var dict=[],map=[],ind=0;
			var r=str.replace(/[0-9A-Za-z_]+/g,function(s){var p;if((p=dict.indexOf(s))!=-1) return map[p]; dict.push(s);map.push(s=nextwd()); return s});
			if(!!sep===sep?sep:defsep) return {dict:dict.join("|"),str:r};
			else return r.length.toString()+":"+r+dict.join("|");
		}
		tt.from = function(data) {
			var str,dict;
			if(typeof data == "object" && "str" in data && "dict" in data) {str=data.str; dict=data.dict}
			else if(typeof data == "string") {var i=data.indexOf(":")+1,j=+data.slice(0,i-1);str=data.slice(i,i+j);dict=data.slice(i+j)}
			else throw "Error: Invalid data for encode.codepack.from.";
			dict=dict.split("|");
			
			function strval(n){for(var i=0,v=0,e=1,l=n.length;i<l;i++){v+=pakal.indexOf(n[i])*e;e*=pakal.length};map[v]=n;return v}
			var map=new Array(dict.length),ind=0;
			var r=str.replace(/[0-9A-Za-z_]+/g,function(s){var p;if((p=map.indexOf(s))==-1) p=strval(s);if(p>dict.length) throw "Error: Failed to unpack in encode.codepack.from.";return dict[p]});
			return r;
		}
	}
	var cpk = new t.codepack();
	t.codepack.to=cpk.to; t.codepack.from=cpk.from;
	
	// dependents: dword
	var md5stbl = (function(){return [
				0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
				0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
				0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
				0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
				0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
				0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
				0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
				0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391 ]})(),
		md5msg = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,  1,6,11,0,5,10,15,4,9,14,3,8,13,2,7,12,
				  5,8,11,14,1,4,7,10,13,0,3,6,9,12,15,2,  0,7,14,5,12,3,10,1,8,15,6,13,4,11,2,9 ],
		md5shf = [7,12,17,22,  5,9,14,20,  4,11,16,23,  6,10,15,21];
	t.md5 = function(iv) {var tt=this; if(!(tt instanceof t.md5)) throw "Bad Instantiation of encode.md5";
		var series = [
			function F(x,y,z) {return ((x&y)|(~x&z))>>>0},
			function G(x,y,z) {return ((x&z)|(y&~z))>>>0},
			function H(x,y,z) {return (x^y^z)>>>0},
			function I(x,y,z) {return (y^(x|(~z)))>>>0}
		];
		
		function digest(iter,a,b,c,d,i,j,k,M) {return (b+bitrot((a+series[iter](b,c,d)+M[i]+md5stbl[k])>>>0,j))>>>0}
		
		if(typeof iv!="string" || !iv.length) iv="\x01\x23\x45\x67\x89\xab\xcd\xef\xfe\xdc\xba\x98\x76\x54\x32\x10";
		if(iv.length<16) iv=strrep(iv,(16/iv.length|0)+1).slice(0,16);
		var iA = dwd.from(iv.slice(0,4)), iB = dwd.from(iv.slice(4,8)), iC = dwd.from(iv.slice(8,12)), iD = dwd.from(iv.slice(12,16));
		
		tt.hash = function(data) {
			var l=data.length;
			data+="\x80"+strrep("\x00",63-(l+8)%64)+dwd.to((l*8)&0xFFFFFFFF)+dwd.to((l/0x20000000)&0xFFFFFFFF);
			
			var A=iA, B=iB, C=iC, D=iD, M = new (w.Uint32Array||Array)(16);
			var a,b,c,d,iter,shv;
			for(var i=0,j;i<data.length;i+=64) {
				for(j=0;j<16;) M[j]=dwd.from(data.slice(i+(j++)*4,i+j*4));
				a=A;b=B;c=C;d=D;
				for(j=0;j<64;) {
					iter=j/16|0;
					shv=iter*4;
					a=digest(iter,a,b,c,d,md5msg[j],md5shf[shv],j,M); j++;
					d=digest(iter,d,a,b,c,md5msg[j],md5shf[shv+1],j,M); j++;
					c=digest(iter,c,d,a,b,md5msg[j],md5shf[shv+2],j,M); j++;
					b=digest(iter,b,c,d,a,md5msg[j],md5shf[shv+3],j,M); j++;
				}
				A=(A+a)>>>0; B=(B+b)>>>0; C=(C+c)>>>0; D=(D+d)>>>0;
			}
			return dwd.to(A)+dwd.to(B)+dwd.to(C)+dwd.to(D);
		}
	}
	var md5 = new t.md5();
	t.md5.hash=md5.hash;
	
	// dependents: dword
	t.sha1 = function(iv,kvec) {var tt=this; if(!(tt instanceof t.sha1)) throw "Bad Instantiation of encode.sha1";
		var xor=function(b,c,d) {return (b^c^d)>>>0};
		var series = [
			function(b,c,d) {return ((b&c)|(~b&d))>>>0},xor,
			function(b,c,d) {return ((b&c)|(b&d)|(c&d))>>>0},xor
		];
		
		function digest(iter,t,a,b,c,d,e,M) {return (bitrot(a,5)+series[iter](b,c,d)+e+M[t]+k[iter])>>>0}
		
		if(typeof kvec!="string" || !kvec.length) kvec="\x99\x79\x82\x5a\xa1\xeb\xd9\x6e\xdc\xbc\x1b\x8f\xd6\xc1\x62\xca";
		if(kvec.length<16) kvec=strrep(kvec,(16/kvec.length|0)+1).slice(0,16);
		var k = [dwd.from(kvec.slice(0,4)), dwd.from(kvec.slice(4,8)), dwd.from(kvec.slice(8,12)), dwd.from(kvec.slice(12,16))];
		
		if(typeof iv!="string" || !iv.length) iv="\x01\x23\x45\x67\x89\xab\xcd\xef\xfe\xdc\xba\x98\x76\x54\x32\x10\xf0\xe1\xd2\xc3";
		if(iv.length<20) iv=strrep(iv,(20/iv.length|0)+1).slice(0,20);
		var iA = dwd.from(iv.slice(0,4)), iB = dwd.from(iv.slice(4,8)), iC = dwd.from(iv.slice(8,12)), iD = dwd.from(iv.slice(12,16)), iE = dwd.from(iv.slice(16,20));
		
		tt.hash = function(data) {
			var l=data.length;
			data+="\x80"+strrep("\x00",63-(l+8)%64)+dwdbe.to((l/0x20000000)&0xFFFFFFFF)+dwdbe.to((l*8)&0xFFFFFFFF);
			
			var A=iA, B=iB, C=iC, D=iD, E=iE, M = new (w.Uint32Array||Array)(16);
			var a,b,c,d,e, v;
			for(var i=0,j,_j;i<data.length;i+=64) {
				for(j=0;j<16;) M[j]=dwdbe.from(data.slice(i+(j++)*4,i+j*4));
				a=A;b=B;c=C;d=D;e=E;
				for(j=0;j<80;j++) {_j=j&15;
					if(j>15) M[_j] = bitrot((M[(j-3)&15] ^ M[(j-8)&15] ^ M[(j-14)&15] ^ M[_j])>>>0,1);
					v=digest(j/20|0,_j,a,b,c,d,e,M);
					e=d;d=c;c=bitrot(b,30);b=a;a=v;
				}
				A=(A+a)>>>0; B=(B+b)>>>0; C=(C+c)>>>0; D=(D+d)>>>0; E=(E+e)>>>0;
			}
			return dwdbe.to(A)+dwdbe.to(B)+dwdbe.to(C)+dwdbe.to(D)+dwdbe.to(E);
		}
	}
	var sh1=new t.sha1();
	t.sha1.hash=sh1.hash;
	
	var sh2t256 = (function(){return [
			0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
			0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
			0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
			0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
			0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
			0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
			0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
			0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 ]})(),
		sh2t512 = (function(){return [
			0x428a2f98,0xd728ae22,  0x71374491,0x23ef65cd,  0xb5c0fbcf,0xec4d3b2f,  0xe9b5dba5,0x8189dbbc,
			0x3956c25b,0xf348b538,  0x59f111f1,0xb605d019,  0x923f82a4,0xaf194f9b,  0xab1c5ed5,0xda6d8118,
			0xd807aa98,0xa3030242,  0x12835b01,0x45706fbe,  0x243185be,0x4ee4b28c,  0x550c7dc3,0xd5ffb4e2,
			0x72be5d74,0xf27b896f,  0x80deb1fe,0x3b1696b1,  0x9bdc06a7,0x25c71235,  0xc19bf174,0xcf692694,
			0xe49b69c1,0x9ef14ad2,  0xefbe4786,0x384f25e3,  0x0fc19dc6,0x8b8cd5b5,  0x240ca1cc,0x77ac9c65,
			0x2de92c6f,0x592b0275,  0x4a7484aa,0x6ea6e483,  0x5cb0a9dc,0xbd41fbd4,  0x76f988da,0x831153b5,
			0x983e5152,0xee66dfab,  0xa831c66d,0x2db43210,  0xb00327c8,0x98fb213f,  0xbf597fc7,0xbeef0ee4,
			0xc6e00bf3,0x3da88fc2,  0xd5a79147,0x930aa725,  0x06ca6351,0xe003826f,  0x14292967,0x0a0e6e70,
			0x27b70a85,0x46d22ffc,  0x2e1b2138,0x5c26c926,  0x4d2c6dfc,0x5ac42aed,  0x53380d13,0x9d95b3df,
			0x650a7354,0x8baf63de,  0x766a0abb,0x3c77b2a8,  0x81c2c92e,0x47edaee6,  0x92722c85,0x1482353b,
			0xa2bfe8a1,0x4cf10364,  0xa81a664b,0xbc423001,  0xc24b8b70,0xd0f89791,  0xc76c51a3,0x0654be30,
			0xd192e819,0xd6ef5218,  0xd6990624,0x5565a910,  0xf40e3585,0x5771202a,  0x106aa070,0x32bbd1b8,
			0x19a4c116,0xb8d2d0c8,  0x1e376c08,0x5141ab53,  0x2748774c,0xdf8eeb99,  0x34b0bcb5,0xe19b48a8,
			0x391c0cb3,0xc5c95a63,  0x4ed8aa4a,0xe3418acb,  0x5b9cca4f,0x7763e373,  0x682e6ff3,0xd6b2b8a3,
			0x748f82ee,0x5defb2fc,  0x78a5636f,0x43172f60,  0x84c87814,0xa1f0ab72,  0x8cc70208,0x1a6439ec,
			0x90befffa,0x23631e28,  0xa4506ceb,0xde82bde9,  0xbef9a3f7,0xb2c67915,  0xc67178f2,0xe372532b,
			0xca273ece,0xea26619c,  0xd186b8c7,0x21c0c207,  0xeada7dd6,0xcde0eb1e,  0xf57d4f7f,0xee6ed178,
			0x06f067aa,0x72176fba,  0x0a637dc5,0xa2c898a6,  0x113f9804,0xbef90dae,  0x1b710b35,0x131c471b,
			0x28db77f5,0x23047d84,  0x32caab7b,0x40c72493,  0x3c9ebe0a,0x15c9bebc,  0x431d67c4,0x9c100d4c,
			0x4cc5d4be,0xcb3e42b6,  0x597f299c,0xfc657e2a,  0x5fcb6fab,0x3ad6faec,  0x6c44198c,0x4a475817 ]})();
	// dependents: dword
	t.sha2 = function(bits,iv) {var tt=this; if(!(tt instanceof t.sha2)) throw "Bad Instantiation of encode.sha2";
		if(+bits!==bits || (bits!==224 && bits!==256 && bits!==384 && bits!==512)) bits=256;
		var bt1,bt2,sig0,sig1,sg0,sg1, rot64,shf64;
		if(bits<257) { // 224/256-bit
			if(typeof iv!="string" || !iv.length)
				iv = bits==224?
					 "\xd8\x9e\x05\xc1\x07\xd5\x7c\x36\x17\xdd\x70\x30\x39\x59\x0e\xf7"
					+"\x31\x0b\xc0\xff\x11\x15\x58\x68\xa7\x8f\xf9\x64\xa4\x4f\xfa\xbe"  // 224
				  :  "\x67\xe6\x09\x6a\x85\xae\x67\xbb\x72\xf3\x6e\x3c\x3a\xf5\x4f\xa5"
					+"\x7f\x52\x0e\x51\x8c\x68\x05\x9b\xab\xd9\x83\x1f\x19\xcd\xe0\x5b"; // 256
			if(iv.length<32) iv=strrep(iv,(32/iv.length|0)+1).slice(0,32);
			var iA = dwd.from(iv.slice(0,4)), iB = dwd.from(iv.slice(4,8)), iC = dwd.from(iv.slice(8,12)), iD = dwd.from(iv.slice(12,16)),
				iE = dwd.from(iv.slice(16,20)), iF = dwd.from(iv.slice(20,24)), iG = dwd.from(iv.slice(24,28)), iH = dwd.from(iv.slice(28,32));
			
			bt1 = function(x,y,z) {return ((x&y)^(~x&z))>>>0}
			bt2 = function(x,y,z) {return ((x&y)^(x&z)^(y&z))>>>0}
			sig0 = function(x) {return (bitrot(x,30)^bitrot(x,19)^bitrot(x,10))>>>0}	// 32-2, 32-13, 32-22
			sig1 = function(x) {return (bitrot(x,26)^bitrot(x,21)^bitrot(x,7))>>>0}		// 32-6, 32-11, 32-25
			sg0 = function(x) {return (bitrot(x,25)^bitrot(x,14)^(x>>>3))>>>0}			// 32-7, 32-18
			sg1 = function(x) {return (bitrot(x,15)^bitrot(x,13)^(x>>>10))>>>0}			// 32-17, 32-19
			
			tt.hash = function(data) {
				var l=data.length;
				data+="\x80"+strrep("\x00",63-(l+8)%64)+dwdbe.to((l/0x20000000)&0xFFFFFFFF)+dwdbe.to((l*8)&0xFFFFFFFF);
				
				var A=iA, B=iB, C=iC, D=iD, E=iE, F=iF, G=iG, H=iH, M = new (w.Uint32Array||Array)(16);
				var a,b,c,d,e,f,g,h, u,v;
				for(var i=0,j,_j;i<data.length;i+=64) {
					for(j=0;j<16;) M[j]=dwdbe.from(data.slice(i+(j++)*4,i+j*4));
					a=A;b=B;c=C;d=D;e=E;f=F;g=G;h=H;
					for(j=0;j<64;j++) {_j=j&15;
						if(j>15) M[_j] = (sg1(M[(j-2)&15])+M[(j-7)&15]+sg0(M[(j-15)&15])+M[_j])>>>0;
						u=(h+sig1(e)+bt1(e,f,g)+sh2t256[j]+M[_j])>>>0; v=(u+sig0(a)+bt2(a,b,c))>>>0;
						h=g;g=f;f=e;e=(d+u)>>>0;d=c;c=b;b=a;a=v;
					}
					A=(A+a)>>>0; B=(B+b)>>>0; C=(C+c)>>>0; D=(D+d)>>>0;
					E=(E+e)>>>0; F=(F+f)>>>0; G=(G+g)>>>0; H=(H+h)>>>0;
				}
				return	dwdbe.to(A)+dwdbe.to(B)+dwdbe.to(C)+dwdbe.to(D)
					+	dwdbe.to(E)+dwdbe.to(F)+dwdbe.to(G)+(bits==224?"":dwdbe.to(H));
			}
		}
		else { // 384/512-bit
			if(typeof iv!="string" || !iv.length)
				iv = bits==384?
					 "\xd8\x9e\x05\xc1\x5d\x9d\xbb\xcb\x07\xd5\x7c\x36\x2a\x29\x9a\x62"
					+"\x17\xdd\x70\x30\x5a\x01\x59\x91\x39\x59\x0e\xf7\xd8\xec\x2f\x15"
					+"\x31\x0b\xc0\xff\x67\x26\x33\x67\x11\x15\x58\x68\x87\x4a\xb4\x8e"
					+"\xa7\x8f\xf9\x64\x0d\x2e\x0c\xdb\xa4\x4f\xfa\xbe\x1d\x48\xb5\x47"  // 384
				  :  "\x08\xc9\xbc\xf3\x67\xe6\x09\x6a\x3b\xa7\xca\x84\x85\xae\x67\xbb"
					+"\x2b\xf8\x94\xfe\x72\xf3\x6e\x3c\xf1\x36\x1d\x5f\x3a\xf5\x4f\xa5"
					+"\xd1\x82\xe6\xad\x7f\x52\x0e\x51\x1f\x6c\x3e\x2b\x8c\x68\x05\x9b"
					+"\x6b\xbd\x41\xfb\xab\xd9\x83\x1f\x79\x21\x7e\x13\x19\xcd\xe0\x5b"; // 512
			if(iv.length<64) iv=strrep(iv,(64/iv.length|0)+1).slice(0,64);
			var iA = [dwd.from(iv.slice(4,8)), dwd.from(iv.slice(0,4))], iB = [dwd.from(iv.slice(12,16)), dwd.from(iv.slice(8,12))],
				iC = [dwd.from(iv.slice(20,24)), dwd.from(iv.slice(16,20))], iD = [dwd.from(iv.slice(28,32)), dwd.from(iv.slice(24,28))],
				iE = [dwd.from(iv.slice(36,40)), dwd.from(iv.slice(32,36))], iF = [dwd.from(iv.slice(44,48)), dwd.from(iv.slice(40,44))],
				iG = [dwd.from(iv.slice(52,56)), dwd.from(iv.slice(48,52))], iH = [dwd.from(iv.slice(60,64)), dwd.from(iv.slice(56,60))];
			
			// rot64 and shf64 are buggy outside this context, and are not to be used thusly
			rot64 = function(x0,x1,b) {return [b<32?(((x1<<32-b)|(x0>>>b))>>>0):(((x1>>>b-32)|(x0<<64-b))>>>0),
											   b<32?(((x0<<32-b)|(x1>>>b))>>>0):(((x0>>>b-32)|(x1<<64-b))>>>0)]}
			shf64 = function(x0,x1,b) {return [x0>>>b,((x0<<32-b)|(x1>>>b))>>>0]}
			
			bt1 = function(x0,x1,y0,y1,z0,z1) {return [((x0&y0)^(~x0&z0))>>>0,((x1&y1)^(~x1&z1))>>>0]}
			bt2 = function(x0,x1,y0,y1,z0,z1) {return [((x0&y0)^(x0&z0)^(y0&z0))>>>0,((x1&y1)^(x1&z1)^(y1&z1))>>>0]}
			sig0 = function(x0,x1) {var a=rot64(x0,x1,28),b=rot64(x0,x1,34),c=rot64(x0,x1,39);return [(a[0]^b[0]^c[0])>>>0, (a[1]^b[1]^c[1])>>>0]}
			sig1 = function(x0,x1) {var a=rot64(x0,x1,14),b=rot64(x0,x1,18),c=rot64(x0,x1,41);return [(a[0]^b[0]^c[0])>>>0, (a[1]^b[1]^c[1])>>>0]}
			sg0 = function(x0,x1) {var a=rot64(x0,x1,1),b=rot64(x0,x1,8),c=shf64(x0,x1,7);return [(a[0]^b[0]^c[0])>>>0, (a[1]^b[1]^c[1])>>>0]}
			sg1 = function(x0,x1) {var a=rot64(x0,x1,19),b=rot64(x0,x1,61),c=shf64(x0,x1,6);return [(a[0]^b[0]^c[0])>>>0, (a[1]^b[1]^c[1])>>>0]}
			
			tt.hash = function(data) {
				var l=data.length;
				data+="\x80"+strrep("\x00",135-(l+16)%128)+dwdbe.to((l/0x20000000)&0xFFFFFFFF)+dwdbe.to((l*8)&0xFFFFFFFF);
				
				var ar=w.Uint32Array||Array;
				var A=new ar(iA), B=new ar(iB), C=new ar(iC), D=new ar(iD),
					E=new ar(iE), F=new ar(iF), G=new ar(iG), H=new ar(iH),
					M = new ar(32);
				var a=new ar(2),b=new ar(2),c=new ar(2),d=new ar(2),
					e=new ar(2),f=new ar(2),g=new ar(2),h=new ar(2), p,q,r,s,s0,s1,x,p0,p1;
				for(var i=0,j,_j,ji;i<data.length;i+=128) {
					for(j=0;j<64;) M[j]=dwdbe.from(data.slice(i+(j++)*4,i+j*4));
					a[0]=A[0];b[0]=B[0];c[0]=C[0];d[0]=D[0];e[0]=E[0];f[0]=F[0];g[0]=G[0];h[0]=H[0];
					a[1]=A[1];b[1]=B[1];c[1]=C[1];d[1]=D[1];e[1]=E[1];f[1]=F[1];g[1]=G[1];h[1]=H[1];
					for(j=0;j<80;j++) {_j=j&15; ji=_j*2;
						if(j>15) {
							x=((j-15)&15)*2; s0 = sg0(M[x],M[x+1]);
							x=((j-2)&15)*2; s1 = sg1(M[x],M[x+1]);
							x=((j-7)&15)*2;
							p0 = s1[0]+M[x]+s0[0]+M[ji];
							p1 = s1[1]+M[x+1]+s0[1]+M[ji+1];
							M[ji]=(p0+p1/0x100000000)>>>0;
							M[ji+1]=p1>>>0;
						}
						p=sig1(e[0],e[1]); q=bt1(e[0],e[1],f[0],f[1],g[0],g[1]);
						r=sig0(a[0],a[1]); s=bt2(a[0],a[1],b[0],b[1],c[0],c[1]);
						s0 = [h[0]+p[0]+q[0]+sh2t512[j*2]+M[ji], h[1]+p[1]+q[1]+sh2t512[j*2+1]+M[ji+1]];
						s0[0] = (s0[0]+s0[1]/0x100000000)>>>0; s0[1]=s0[1]>>>0;
						s1 = [r[0]+s[0], r[1]+s[1]];
						s1[0] = (s1[0]+s1[1]/0x100000000)>>>0; s1[1]=s1[1]>>>0;
						x=h;h=g;g=f;f=e;e=d;
						p0=e[0]+s0[0]; p1=e[1]+s0[1];
						e[0] = (p0+p1/0x100000000)>>>0; e[1]=p1>>>0;
						d=c;c=b;b=a;a=x;
						p0=s0[0]+s1[0]; p1=s0[1]+s1[1];
						a[0] = (p0+p1/0x100000000)>>>0; a[1]=p1>>>0;
					}
					p0=A[0]+a[0]; p1=A[1]+a[1]; A[0]=(p0+p1/0x100000000)>>>0; A[1]=p1>>>0;
					p0=B[0]+b[0]; p1=B[1]+b[1]; B[0]=(p0+p1/0x100000000)>>>0; B[1]=p1>>>0;
					p0=C[0]+c[0]; p1=C[1]+c[1]; C[0]=(p0+p1/0x100000000)>>>0; C[1]=p1>>>0;
					p0=D[0]+d[0]; p1=D[1]+d[1]; D[0]=(p0+p1/0x100000000)>>>0; D[1]=p1>>>0;
					p0=E[0]+e[0]; p1=E[1]+e[1]; E[0]=(p0+p1/0x100000000)>>>0; E[1]=p1>>>0;
					p0=F[0]+f[0]; p1=F[1]+f[1]; F[0]=(p0+p1/0x100000000)>>>0; F[1]=p1>>>0;
					p0=G[0]+g[0]; p1=G[1]+g[1]; G[0]=(p0+p1/0x100000000)>>>0; G[1]=p1>>>0;
					p0=H[0]+h[0]; p1=H[1]+h[1]; H[0]=(p0+p1/0x100000000)>>>0; H[1]=p1>>>0;
				}
				return dwdbe.to(A[0])+dwdbe.to(A[1])+dwdbe.to(B[0])+dwdbe.to(B[1])
					+  dwdbe.to(C[0])+dwdbe.to(C[1])+dwdbe.to(D[0])+dwdbe.to(D[1])
					+  dwdbe.to(E[0])+dwdbe.to(E[1])+dwdbe.to(F[0])+dwdbe.to(F[1])
	  + (bits==384?"": dwdbe.to(G[0])+dwdbe.to(G[1])+dwdbe.to(H[0])+dwdbe.to(H[1]));
			}
		}
	}
	var sha2=new t.sha2();
	t.sha2.hash=sha2.hash;
	
	t.buffermath = function(wordsz,msb) {var tt=this; if(!(tt instanceof t.buffermath)) throw "Bad Instantiation of encode.buffermath";
		if(wordsz!==1 && wordsz!==2 && wordsz!==3 && wordsz!==4 && wordsz!==5 && wordsz!==6 && wordsz!=="unicode") wordsz=1;
		msb=!!msb;
		var read,write,mask;
		if(wordsz==="unicode") { read=function(o) {return o.s[cca](o.i++)}
			write=function(v) {return chr(v)}
			mask=0xFFFFFFFF; }
		else if(wordsz==1) { read=function(o) {return o.s[cca](o.i++)&0xFF}
			write=function(v) {return chr(v)}
			mask=0xFF; }
		else if(msb) { read=function(o) {for(var i=0,v=0;i<wordsz;i++) v=(v<<8)|(o.s[cca](o.i++)&0xFF); return v}
			write=function(v) {for(var i=wordsz-1,o="";i>=0;i--) o+=chr((v>>i*8)&0xFF); return o}
			mask=(1<<wordsz*8)-1; }
		else { read=function(o) {for(var i=0,v=0;i<wordsz;i++) v|=(o.s[cca](o.i++)&0xFF)<<i*8; return v}
			write=function(v) {for(var i=0,o="";i<wordsz;i++) o+=chr((v>>i*8)&0xFF); return o}
			mask=(1<<wordsz*8)-1; }
		function norm(o,l) {
			if(o.s.length<l) o.s+=strrep("\0",l-o.s.length);
		}
		
		var wmax=1<<wordsz*8;
		
		function gencombin(a,b,l,f) {
			var ao={i:0,s:a},bo={i:0,s:b};
			norm(ao,l*wordsz); norm(bo,l*wordsz);
			for(var i=0,o="";i<l;i++)
				o+=write(f(ao,bo,read,wordsz,wmax)&mask);
			return o;
		}
		function genmono(a,l,f) {
			var ao={i:0,s:a};
			norm(ao,l*wordsz);
			for(var i=0,o="";i<l;i++)
				o+=write(f(ao,read,wordsz,wmax)&mask);
			return o;
		}
		
		tt.add = function(a,b,l) {
			return gencombin(a,b,l,function(a,b,read){return read(a)+read(b)});
		}
		tt.sub = function(a,b,l) {
			return gencombin(a,b,l,function(a,b,read){return read(a)-read(b)});
		}
		tt.mul = function(a,b,l) {
			return gencombin(a,b,l,function(a,b,read){return read(a)*read(b)});
		}
		tt.mmul = function(a,b,l) {
			return gencombin(a,b,l,function(a,b,read,wsz,mx){return read(a)*read(b)%(mx+1)})
		}
		tt.div = function(a,b,l) {
			return gencombin(a,b,l,function(a,b,read){b=read(b); return b==0?0:read(a)/b});
		}
		tt.and = function(a,b,l) {
			return gencombin(a,b,l,function(a,b,read){return read(a)&read(b)});
		}
		tt.or = function(a,b,l) {
			return gencombin(a,b,l,function(a,b,read){return read(a)|read(b)});
		}
		tt.xor = function(a,b,l) {
			return gencombin(a,b,l,function(a,b,read){return read(a)^read(b)});
		}
		tt.neg = function(a,l) {
			return genmono(a,l,function(a,read,wsz,mx){return mx-read(a)});
		}
		tt.inv = function(a,l) {
			return genmono(a,l,function(a,read){return ~read(a)});
		}
		tt.imul = function(a,l) {
			return genmono(a,l,function(a,read,wsz,mx){
					var r0=read(a),r1=++mx,r2,s0=1,s1=0,s2,q;
					do {q=r0/r1|0;
						r2=r0-q*r1; s2=s0-q*s1;
						r0=r1;r1=r2; s0=s1;s1=s2;
					} while(r2);
					if(s0<0) s0+=mx;
					return s0;
				});
		}
		tt.customcombine = function(a,b,l,f) {
			return gencombin(a,b,l,f);
		}
		tt.custommono = function(a,l,f) {
			return genmono(a,l,f);
		}
	}
	var bufm=new t.buffermath();
	;(function(){for(var i in bufm) t.buffermath[i]=bufm[i]})();
	
	var cmodes=["ecb","cbc","pcbc","cfb","cfb8","ofb","ofb8","ctr"],cmodes_ht={};
	t.bcmode = function(cb,iv) {var tt=this; if(!(tt instanceof t.bcmode)) throw "Bad Instantiation of encode.bcmode";
		if(+cb!==cb) cb=cmodes_ht[cb]||0;
		if(typeof iv!="string") iv="";
		function xorbufs(a,b,l) {
			for(var i=0,o="";i<l;i++)
				o+=chr((a[cca](i)^b[cca](i))&255);
			return o;
		}
		function norm(a,l) {
			if(a.length<l) a+=strrep("\0",l-a.length); else a=a.slice(0,l);
			return a;
		}
		
		tt.initvector = function(v) {
			if(v===undef) return iv;
			if(typeof v=="string") iv=v;
		}
		tt.mode = function(_cb) {
			if(_cb===undef) return cb;
			if(_cb==="string") return cmodes[cb];
			if(typeof _cb=="string" && cmodes_ht[_cb]) cb=cmodes_ht[_cb];
			if(_cb in cmodes) cb=_cb;
		}
		tt.prepare = function(enc) {
			switch(cb) {
				case 0: // ecb
					return {enc:enc,dec:!enc,dir:1,mode:enc};
				case 1: // cbc
					return {enc:enc,dec:!enc,dir:1,mode:enc};
				case 2: // pcbc
					return {enc:enc,dec:!enc,dir:1,mode:enc};
				case 3: // cfb
					return {enc:true,dec:false,dir:1,mode:enc};
				case 4: // cfb8
					return {enc:true,dec:false,dir:1,mode:enc,stream:true};
				case 5: // ofb
					return {enc:true,dec:false,dir:1,mode:enc};
				case 6: // ofb8
					return {enc:true,dec:false,dir:1,mode:enc,stream:true};
				case 7: // ctr
					return {enc:true,dec:false,dir:1,mode:enc};
				default: // internal error
					return {enc:false,dec:false,dir:0,mode:enc};
			}
		}
		tt.run = function(fnc,obj,msg,cksize) {
			var v=norm(iv,cksize);
			var o="";
			var mode=obj.mode;
			switch(cb) {
				case 0: // ecb
					for(var i=0;i<msg.length;i+=cksize) {
						o+=fnc(msg.slice(i,i+cksize),i);
					}
					break;
				case 1: // cbc
					if(mode) {
						for(var i=0;i<msg.length;i+=cksize) {
							v=fnc(xorbufs(v,msg.slice(i,i+cksize),cksize),i);
							o+=v;
						}
					} else {
						for(var i=0,ch=v;i<msg.length;i+=cksize) {
							v=msg.slice(i,i+cksize);
							o+=xorbufs(ch,fnc(v,i),cksize);
							ch=v;
						}
					}
					break;
				case 2: // pcbc
					if(mode) {
						for(var i=0,bef,aft;i<msg.length;i+=cksize) {
							bef=msg.slice(i,i+cksize);
							aft=fnc(xorbufs(v,bef,cksize),i);
							o+=aft; v=xorbufs(bef,aft);
						}
					} else {
						for(var i=0,bef,aft;i<msg.length;i+=cksize) {
							bef=msg.slice(i,i+cksize);
							aft=xorbufs(v,fnc(bef,i),cksize);
							o+=aft; v=xorbufs(bef,aft,cksize);
						}
					}
					break;
				case 3: // cfb
					if(mode) {
						for(var i=0;i<msg.length;i+=cksize) {
							v=xorbufs(msg.slice(i,i+cksize),fnc(v,i),cksize);
							o+=v;
						}
					} else {
						for(var i=0,ch;i<msg.length;i+=cksize) {
							ch=msg.slice(i,i+cksize);
							v=xorbufs(ch,fnc(v,i),cksize);
							o+=v; v=ch;
						}
					}
					break;
				case 4: // cfb8
					if(mode) {
						for(var i=0;i<msg.length;i++) {
							v=v.slice(1)+xorbufs(msg.slice(i,i+1),fnc(v,i),1);
							o+=v.slice(-1);
						}
					} else {
						for(var i=0,ch;i<msg.length;i++) {
							ch=fnc(v,i)[0];
							v=v.slice(1)+msg.slice(i,i+1);
							o+=xorbufs(v.slice(-1),ch,1);
						}
					}
					break;
				case 5: // ofb
					for(var i=0;i<msg.length;i+=cksize) {
						v=fnc(v,i);
						o+=xorbufs(v,msg.slice(i,i+cksize),cksize);
					}
					break;
				case 6: // ofb8
					for(var i=0;i<msg.length;i++) {
						v=v.slice(1)+fnc(v,i)[0];
						o+=xorbufs(msg.slice(i,i+1),v.slice(-1),1);
					}
					break;
				case 7: // ctr
					for(var i=0,j,n,ctr=strrep("\0",cksize);i<msg.length;i+=cksize) {
						j=cksize; while(j-- >0) {
							n=ctr[cca](j)+1;
							ctr=ctr.slice(0,j)+chr(n&0xFF)+ctr.slice(j+1);
							if(n<256) break;
						}
						o+=xorbufs(msg.slice(i,i+cksize),fnc(xorbufs(v,ctr,cksize),i),cksize);
					}
					break;
			}
			return o;
		}
	}
	;(function(){for(var i=0;i<cmodes.length;i++) t.bcmode[cmodes[i]]=cmodes_ht[cmodes[i]]=i})();
	var bcm=new t.bcmode();
	
	// dependents: bcmode
	var aestbl = (function(){return [
			0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
			0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
			0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
			0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
			0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
			0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
			0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
			0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
			0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
			0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
			0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
			0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
			0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
			0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
			0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
			0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16
		]})();
	var aesitbl = (function(){var tbl=new Array(256); for(var i=0;i<256;i++) tbl[aestbl[i]]=i; return tbl})();
	t.aes = function(bits,bksize,defbcm) {var tt=this; if(!(tt instanceof t.aes)) throw "Bad Instantiation of encode.aes";
		if(bksize!==128 && bksize!==192 && bksize!==256) bksize=128;
		if(bits!==128 && bits!==192 && bits!==256) bits=256;
		if(!(defbcm instanceof t.bcmode)) defbcm=bcm;
		var nk=bits/8,nb=bksize/8,nr=Math.max(nk/4,nb/4)+6;
		
		function xtime(x) {return ((x<<1)^((x&0x80)?0x1b:0))&0xFF}
		function subbytes(stt) {for(var i=0;i<nb;i++) stt[i]=aestbl[stt[i]]}
		var shiftrows=nb==16? function(stt) {
				var t=stt[1];stt[1]=stt[5];stt[5]=stt[9];stt[9]=stt[13];stt[13]=t;
				t=stt[2];stt[2]=stt[10];stt[10]=t;t=stt[6];stt[6]=stt[14];stt[14]=t;
				t=stt[15];stt[15]=stt[11];stt[11]=stt[7];stt[7]=stt[3];stt[3]=t;
			} : nb==24? function(stt) {
				var t=stt[1];stt[1]=stt[5];stt[5]=stt[9];stt[9]=stt[13];stt[13]=stt[17];stt[17]=stt[21];stt[21]=t;
				t=stt[2];stt[2]=stt[10];stt[10]=stt[18];stt[18]=t;t=stt[6];stt[6]=stt[14];stt[14]=stt[22];stt[22]=t;
				t=stt[3];stt[3]=stt[15];stt[15]=t;t=stt[7];stt[7]=stt[19];stt[19]=t;t=stt[11];stt[11]=stt[23];stt[23]=t;
			} : function(stt) {
				var t=stt[1];stt[1]=stt[5];stt[5]=stt[9];stt[9]=stt[13];stt[13]=stt[17];stt[17]=stt[21];stt[21]=stt[25];stt[25]=stt[29];stt[29]=t;
				t=stt[2];stt[2]=stt[14];stt[14]=stt[26];stt[26]=stt[6];stt[6]=stt[18];stt[18]=stt[30];stt[30]=stt[10];stt[10]=stt[22];stt[22]=t;
				t=stt[3];stt[3]=stt[19];stt[19]=t;t=stt[7];stt[7]=stt[23];stt[23]=t;t=stt[11];stt[11]=stt[27];stt[27]=t;t=stt[15];stt[15]=stt[31];stt[31]=t;
			};
		function mixcolumns(stt) {
			var a,b,c,d,e,i;
			for(i=0;i<nb;i+=4) {
				a=stt[i];b=stt[i+1];c=stt[i+2];d=stt[i+3];
				e=a^b^c^d;
				stt[i]	^=e^xtime(a^b);
				stt[i+1]^=e^xtime(b^c);
				stt[i+2]^=e^xtime(c^d);
				stt[i+3]^=e^xtime(d^a);
			}
		}
		
		function addroundkey(stt,k,i) {
			for(var j=0;j<nb;j++) stt[j]^=k[i+j];
		}
		
		function isubbytes(stt) {for(var i=0;i<nb;i++) stt[i]=aesitbl[stt[i]]}
		var ishiftrows=nb==16? function(stt) {
				var t=stt[13];stt[13]=stt[9];stt[9]=stt[5];stt[5]=stt[1];stt[1]=t;
				t=stt[10];stt[10]=stt[2];stt[2]=t;t=stt[14];stt[14]=stt[6];stt[6]=t;
				t=stt[3];stt[3]=stt[7];stt[7]=stt[11];stt[11]=stt[15];stt[15]=t;
			} : nb==24? function(stt) {
				var t=stt[21];stt[21]=stt[17];stt[17]=stt[13];stt[13]=stt[9];stt[9]=stt[5];stt[5]=stt[1];stt[1]=t;
				t=stt[18];stt[18]=stt[10];stt[10]=stt[2];stt[2]=t;t=stt[22];stt[22]=stt[14];stt[14]=stt[6];stt[6]=t;
				t=stt[15];stt[15]=stt[3];stt[3]=t;t=stt[19];stt[19]=stt[7];stt[7]=t;t=stt[23];stt[23]=stt[11];stt[11]=t;
			} : function(stt) {
				var t=stt[29];stt[29]=stt[25];stt[25]=stt[21];stt[21]=stt[17];stt[17]=stt[13];stt[13]=stt[9];stt[9]=stt[5];stt[5]=stt[1];stt[1]=t;
				t=stt[22];stt[22]=stt[10];stt[10]=stt[30];stt[30]=stt[18];stt[18]=stt[6];stt[6]=stt[26];stt[26]=stt[14];stt[14]=stt[2];stt[2]=t;
				t=stt[19];stt[19]=stt[3];stt[3]=t;t=stt[23];stt[23]=stt[7];stt[7]=t;t=stt[27];stt[27]=stt[11];stt[11]=t;t=stt[31];stt[31]=stt[15];stt[15]=t;
			};
		function imixcolumns(stt) {
			var a,b,c,d,e,x,y,z,i;
			for(i=0;i<nb;i+=4) {
				a=stt[i];b=stt[i+1];c=stt[i+2];d=stt[i+3];
				e=a^b^c^d; z=xtime(e);
				x=e^xtime(xtime(z^a^c));
				y=e^xtime(xtime(z^b^d));
				stt[i]	^=x^xtime(a^b);
				stt[i+1]^=y^xtime(b^c);
				stt[i+2]^=x^xtime(c^d);
				stt[i+3]^=y^xtime(d^a);
			}
		}
		
		function genkey(k,key) {
			var i,l,rc=1, a,b,c,d;
			for(i=0;i<nk;i++) k[i]=key[cca](i)&0xFF;
			for(i=nk,l=(nr+1)*nb;i<l;i+=4) {
				if(i%nk==0) {
					a=aestbl[k[i-3]]^rc;b=aestbl[k[i-2]];c=aestbl[k[i-1]];d=aestbl[k[i-4]];
					rc=xtime(rc);
				} else if(bits==256 && i%nk==16) {
					a=aestbl[k[i-4]];b=aestbl[k[i-3]];c=aestbl[k[i-2]];d=aestbl[k[i-1]];
				} else {a=k[i-4]; b=k[i-3]; c=k[i-2]; d=k[i-1]}
				k[i]=k[i-nk]^a;k[i+1]=k[i-nk+1]^b;k[i+2]=k[i-nk+2]^c;k[i+3]=k[i-nk+3]^d;
			}
		}
		
		var ar = w.Uint8Array||Array;
		
		function genhash(msg,key,bcm,mode) {
			if(typeof key!="string") key=strrep("\0",nk);
			if(key.length<nk) key+=strrep("\0",nk-key.length);
			var stt = new ar(nb);
			var k=new ar(nb*(nr+1));
			if(!(bcm instanceof t.bcmode)) bcm=defbcm;
			
			genkey(k,key);
			var reqs=bcm.prepare(mode);
			
			if(!reqs.stream) msg+=strrep("\0",nb-(msg.length-1)%nb-1);
			
			var f=reqs.enc ?
				function enc(chk) {var i,o;
					for(i=0;i<nb;i++) stt[i]=chk[cca](i);
					addroundkey(stt,k,0);
					for(i=1;i<nr;i++) {
						subbytes(stt);
						shiftrows(stt);
						mixcolumns(stt);
						addroundkey(stt,k,i*nb);
					}
					subbytes(stt);
					shiftrows(stt);
					addroundkey(stt,k,nr*nb);
					for(i=0,o="";i<nb;i++) o+=chr(stt[i]);
					return o;
				} :
				function dec(chk) {var i,o;
					for(i=0;i<nb;i++) stt[i]=chk[cca](i);
					addroundkey(stt,k,nr*nb);
					for(i=nr-1;i>0;i--) {
						ishiftrows(stt);
						isubbytes(stt);
						addroundkey(stt,k,i*nb);
						imixcolumns(stt);
					}
					ishiftrows(stt);
					isubbytes(stt);
					addroundkey(stt,k,0);
					for(i=0,o="";i<nb;i++) o+=chr(stt[i]);
					return o;
				};
			
			return bcm.run(f,reqs,msg,bksize/8);
		}
		
		tt.to = function(msg,key,bcm) {
			return genhash(msg,key,bcm,true)
		}
		tt.from = function(msg,key,bcm) {
			return genhash(msg,key,bcm,false);
		}
	}
	var aes=new t.aes();
	t.aes.to=aes.to; t.aes.from=aes.from;
	
	// dependents: bcmode
	t.idea = function(defbcm) {var tt=this; if(!(tt instanceof t.idea)) throw "Bad Instantiation of encode.idea";
		if(!(defbcm instanceof t.bcmode)) defbcm=bcm;
		
		function genkey(key) {
			var k=[];
			if(key.length<16) key+=strrep("\0",16-key.length);
			for(var i=0;i<8;i+=1)
				k.push((key[cca](i*2)&255)*256+(key[cca](i*2+1)&255));
			for(var b,m,n;i<52;i++) {
				b=(i/8-1|0)*8; m=(i+1)%8+b; n=(i+2)%8+b;        // 25<<
				k.push(((k[m]<<9)&0xFE00)|((k[n]>>7)&0x01FF));
			}
			return k;
		}
		
		function wd(s) {return (s[cca](0)&255)*256+(s[cca](1)&255)}
		function str(wd) {return chr((wd>>8)&255)+chr(wd&255)}
		function invkey(k) {
			var i,s0,s1,s2,r0,r1,r2,q;
			for(var i=0;i<52;i++)
				if(i%6==1 || i%6==2) { // invert addition
					k[i]=65536-k[i] & 0xFFFF;
				} else if(i%6==0 || i%6==3) { // invert multiplier
					r0=k[i]; r1=65537; s0=1; s1=0;
					do {q=r0/r1|0;
						r2=r0-q*r1; s2=s0-q*s1;
						r0=r1;r1=r2; s0=s1;s1=s2;
					} while(r2);
					if(s0<0) s0+=65537; k[i]=s0;
				}
		}
		function normkey(k) {
			for(var i=0;i<52;i+=6) {
				if(k[i]===0) k[i]=65536;
				if(k[i+3]===0) k[i+3]=65536;
				if(k[i+4]===0) k[i+4]=65536;
				if(k[i+5]===0) k[i+5]=65536;
			}
		}
		
		function genhash(msg,key,bcm,mode) {
			if(!(bcm instanceof t.bcmode)) bcm=defbcm;
			if(typeof key!="string") key="";
			var k=genkey(key);
			
			function hbk(st,ki) {
				st[0]=(st[0]||65536)*k[ki]%65537 & 0xFFFF;
				st[1]=st[1]+k[ki+1] & 0xFFFF;
				st[2]=st[2]+k[ki+2] & 0xFFFF;
				st[3]=(st[3]||65536)*k[ki+3]%65537 & 0xFFFF;
			}
			
			var reqs=bcm.prepare(mode);
			
			if(!reqs.stream) msg+=strrep("\0",8-(msg.length-1)%8-1);
			
			var f=reqs.enc ?
				function enc(chk) {
					var st=[wd(chk.slice(0,2)),wd(chk.slice(2,4)),wd(chk.slice(4,6)),wd(chk.slice(6,8))];
					var a,b,v;
					for(var i=0;i<8;i++) {
						if(i) {v=st[1];st[1]=st[2];st[2]=v}
						hbk(st,i*6);
						a=st[0]^st[2]; b=st[1]^st[3];
						a=(a||65536)*k[i*6+4]%65537 & 0xFFFF; b=b+a & 0xFFFF;
						b=(b||65536)*k[i*6+5]%65537 & 0xFFFF; a=a+b & 0xFFFF;
						st[0]^=b; st[1]^=a; st[2]^=b; st[3]^=a;
					}
					hbk(st,48);
					return str(st[0])+str(st[1])+str(st[2])+str(st[3]);
				} :
				function dec(chk) {
					var st=[wd(chk.slice(0,2)),wd(chk.slice(2,4)),wd(chk.slice(4,6)),wd(chk.slice(6,8))];
					var a,b,v;
					for(var i=7;i>=0;i--) {
						hbk(st,i*6+6);
						if(i<7) {v=st[1];st[1]=st[2];st[2]=v}
						a=st[0]^st[2]; b=st[1]^st[3];
						a=(a||65536)*k[i*6+4]%65537 & 0xFFFF; b=b+a & 0xFFFF;
						b=(b||65536)*k[i*6+5]%65537 & 0xFFFF; a=a+b & 0xFFFF;
						st[0]^=b; st[1]^=a; st[2]^=b; st[3]^=a;
					}
					hbk(st,0);
					return str(st[0])+str(st[1])+str(st[2])+str(st[3]);
				};
			if(!reqs.enc) invkey(k);
			normkey(k);
			
			return bcm.run(f,reqs,msg,8);
		}
		
		tt.to = function(msg,key,bcm) {
			return genhash(msg,key,bcm,true);
		}
		tt.from = function(msg,key,bcm) {
			return genhash(msg,key,bcm,false);
		}
	}
	var idea=new t.idea();
	t.idea.to=idea.to; t.idea.from=idea.from;
	
	// dependents: bcmode
	t.salsa20 = function(defbcm) {var tt=this; if(!(tt instanceof t.salsa20)) throw "Bad Instantiation of encode.salsa20";
		if(!(defbcm instanceof t.bcmode)) defbcm=bcm;
		
		function dbrnd(x) {var i,y=x.slice();
			for(i=0;i<10;i++) {
				// horizontal quarterround
				x[4] ^=bitrot(x[0]+x[12]>>>0,7);  x[8] ^=bitrot(x[4]+x[0]>>>0,9);
				x[12]^=bitrot(x[8]+x[4]>>>0,13);  x[0] ^=bitrot(x[12]+x[8]>>>0,18);
				x[9] ^=bitrot(x[5]+x[1]>>>0,7);   x[13]^=bitrot(x[9]+x[5]>>>0,9);
				x[1] ^=bitrot(x[13]+x[9]>>>0,13); x[5] ^=bitrot(x[1]+x[13]>>>0,18);
				x[14]^=bitrot(x[10]+x[6]>>>0,7);  x[2] ^=bitrot(x[14]+x[10]>>>0,9);
				x[6] ^=bitrot(x[2]+x[14]>>>0,13); x[10]^=bitrot(x[6]+x[2]>>>0,18);
				x[3] ^=bitrot(x[15]+x[11]>>>0,7); x[7] ^=bitrot(x[3]+x[15]>>>0,9);
				x[11]^=bitrot(x[7]+x[3]>>>0,13);  x[15]^=bitrot(x[11]+x[7]>>>0,18);
				// vertical quarterround
				x[1] ^=bitrot(x[0]+x[3]>>>0,7);   x[2] ^=bitrot(x[1]+x[0]>>>0,9);
				x[3] ^=bitrot(x[2]+x[1]>>>0,13);  x[0] ^=bitrot(x[3]+x[2]>>>0,18);
				x[6] ^=bitrot(x[5]+x[4]>>>0,7);   x[7] ^=bitrot(x[6]+x[5]>>>0,9);
				x[4] ^=bitrot(x[7]+x[6]>>>0,13);  x[5] ^=bitrot(x[4]+x[7]>>>0,18);
				x[11]^=bitrot(x[10]+x[9]>>>0,7);  x[8] ^=bitrot(x[11]+x[10]>>>0,9);
				x[9] ^=bitrot(x[8]+x[11]>>>0,13); x[10]^=bitrot(x[9]+x[8]>>>0,18);
				x[12]^=bitrot(x[15]+x[14]>>>0,7); x[13]^=bitrot(x[12]+x[15]>>>0,9);
				x[14]^=bitrot(x[13]+x[12]>>>0,13);x[15]^=bitrot(x[14]+x[13]>>>0,18);
			}
			for(i=0;i<16;i++) x[i]=x[i]+y[i]>>>0;
		}
		
		function genhash(msg,bcm,mode) {
			if(!(bcm instanceof t.bcmode)) bcm=defbcm;
			
			var reqs=bcm.prepare(mode);
			if(!reqs.stream) msg+=strrep("\0",63-(msg.length-1)%64);
			
			var stt=new Array(16);
			
			var f=reqs.enc &&
				function enc(chk) {var i,o="";
					for(i=0;i<64;i+=4) stt[i/4] = (chk[cca](i)&255)+(chk[cca](i+1)&255)*256+(chk[cca](i+2)&255)*65536+(chk[cca](i+3)&255)*16777216;
					dbrnd(stt);
					for(i=0;i<16;i++) o+=chr(stt[i]&255)+chr((stt[i]>>8)&255)+chr((stt[i]>>16)&255)+chr((stt[i]>>24)&255);
					return o;
				};
			if(!f) return null;
			
			return bcm.run(f,reqs,msg,64);
		}
		
		tt.hash = function(msg,bcm,reverse) {
			return genhash(msg,bcm,!reverse);
		}
	}
	var s20=new t.salsa20();
	t.salsa20.hash=s20.hash;
	
	// dependents: bcmode
	function des_genscrambler(tbl,bi,bo) {
		var i64=bi>32,o64=bo>32,ipd=31-(bi-1)%32,opd=31-(bo-1)%32;
		var c="return "+(o64?"[(":"("),d;
		
		for(var i=0,j=bo-1;i<bo;i++,j--) {
			d=(i+opd)%32-(tbl[i]+ipd)%32;
			c += (i+opd==32?")>>>0,(":i>0?"|":"")
			  +	 "("
			  +	 "x"+(i64?"["+((tbl[i]+ipd)/32|0)+"]":"")
			  +	 (d?(d<0?"<<":">>")+Math.abs(d):"")
			  +	 "&0x"+((1<<j%32)>>>0).toString(16)
			  +	 ")";
		}
		// return [(x<<4&0x800)|(x<<5&0x400)|...&0x1),(x>>2&0x800)|(...];
		
		c+=o64?")>>>0];":")>>>0;";
		return new Function("x",c);
	}
	var _des={
		s:[	[14,0,4,15,13,7,1,4,2,14,15,2,11,13,8,1,3,10,10,6,6,12,12,11,5,9,9,5,0,3,7,8,4,15,1,12,14,8,8,2,13,4,6,9,2,1,11,7,15,5,12,11,9,3,7,14,3,10,10,0,5,6,0,13], // s1
			[15,3,1,13,8,4,14,7,6,15,11,2,3,8,4,14,9,12,7,0,2,1,13,10,12,6,0,9,5,11,10,5,0,13,14,8,7,10,11,1,10,3,4,15,13,4,1,2,5,11,8,6,12,7,6,12,9,0,3,5,2,14,15,9], // s2
			[10,13,0,7,9,0,14,9,6,3,3,4,15,6,5,10,1,2,13,8,12,5,7,14,11,12,4,11,2,15,8,1,13,1,6,10,4,13,9,0,8,6,15,9,3,8,0,7,11,4,1,15,2,14,12,3,5,11,10,5,14,2,7,12], // s3
			[7,13,13,8,14,11,3,5,0,6,6,15,9,0,10,3,1,4,2,7,8,2,5,12,11,1,12,10,4,14,15,9,10,3,6,15,9,0,0,6,12,10,11,1,7,13,13,8,15,9,1,4,3,5,14,11,5,12,2,7,8,2,4,14], // s4
			[2,14,12,11,4,2,1,12,7,4,10,7,11,13,6,1,8,5,5,0,3,15,15,10,13,3,0,9,14,8,9,6,4,11,2,8,1,12,11,7,10,1,13,14,7,2,8,13,15,6,9,15,12,0,5,9,6,10,3,4,0,5,14,3], // s5
			[12,10,1,15,10,4,15,2,9,7,2,12,6,9,8,5,0,6,13,1,3,13,4,14,14,0,7,11,5,3,11,8,9,4,14,3,15,2,5,12,2,9,8,5,12,15,3,10,7,11,0,14,4,1,10,7,1,6,13,0,11,8,6,13], // s6
			[4,13,11,0,2,11,14,7,15,4,0,9,8,1,13,10,3,14,12,3,9,5,7,12,5,2,10,15,6,8,1,6,1,6,4,11,11,13,13,8,12,1,3,4,7,10,14,7,10,9,15,5,6,0,8,15,0,14,5,2,9,3,2,12], // s7
			[13,1,2,15,8,13,4,8,6,10,15,3,11,7,1,4,10,12,9,5,3,6,14,11,5,0,0,14,12,9,7,2,7,2,11,1,4,14,1,7,9,4,12,10,14,8,2,13,0,15,6,12,10,9,13,0,15,3,3,5,5,6,8,11]  // s8
		],
		IP:	des_genscrambler([57,49,41,33,25,17,9,1,59,51,43,35,27,19,11,3,61,53,45,37,29,21,13,5,63,55,47,39,31,23,15,7,
								56,48,40,32,24,16,8,0,58,50,42,34,26,18,10,2,60,52,44,36,28,20,12,4,62,54,46,38,30,22,14,6],64,64),
		iIP:des_genscrambler([39,7,47,15,55,23,63,31,38,6,46,14,54,22,62,30,37,5,45,13,53,21,61,29,36,4,44,12,52,20,60,28,
								35,3,43,11,51,19,59,27,34,2,42,10,50,18,58,26,33,1,41,9,49,17,57,25,32,0,40,8,48,16,56,24],64,64),
		P:	des_genscrambler([15,6,19,20,28,11,27,16,0,14,22,25,4,17,30,9,1,7,23,13,31,26,2,8,18,12,29,5,21,10,3,24],32,32),
		PC1_C:	des_genscrambler([56,48,40,32,24,16,8,0,57,49,41,33,25,17,9,1,58,50,42,34,26,18,10,2,59,51,43,35],64,28),
		PC1_D:	des_genscrambler([62,54,46,38,30,22,14,6,61,53,45,37,29,21,13,5,60,52,44,36,28,20,12,4,27,19,11,3],64,28),
		PC2:	des_genscrambler([13,16,10,23,0,4,2,27,14,5,20,9,22,18,11,3,25,7,15,6,26,19,12,1,40,51,30,36,46,54,
									29,39,50,44,32,47,43,48,38,55,33,52,45,41,49,35,28,31],56,48),
		E:	des_genscrambler([31,0,1,2,3,4,3,4,5,6,7,8,7,8,9,10,11,12,11,12,13,14,15,16,15,16,
								17,18,19,20,19,20,21,22,23,24,23,24,25,26,27,28,27,28,29,30,31,0],32,48),
		SH:	[1,1,2,2,2,2,2,2,1,2,2,2,2,2,2,1]
	};
	t.des = function(triple,defbcm) {var tt=this; if(!(tt instanceof t.des)) throw "Bad Instantiation of encode.des";
		triple=!!triple; if(!(defbcm instanceof t.bcmode)) defbcm=bcm;
		
		function rot28(x,n) {return (((x<<n)|(x>>28-n))&0x0FFFFFFF)>>>0}
		function feistel(x,k) {
			x=_des.E(x);
			x[0]=(x[0]^k[0])>>>0; x[1]=(x[1]^k[1])>>>0;
			x=((_des.s[0][x[0]>>10&0x3F]<<28)|(_des.s[1][x[0]>>4&0x3F]<<24)|(_des.s[2][(x[0]<<2&0x3C)|(x[1]>>30&0x3)]<<20)|(_des.s[3][x[1]>>24&0x3F]<<16)
				|(_des.s[4][x[1]>>18&0x3F]<<12)|(_des.s[5][x[1]>>12&0x3F]<<8)|(_des.s[6][x[1]>>6&0x3F]<<4)|(_des.s[7][x[1]&0x3F]))>>>0;
			x=_des.P(x);
			return x;
		}
		function cipher(chk,k,dir) {
			var a=chk[cca](0)*16777216+chk[cca](1)*65536+chk[cca](2)*256+chk[cca](3)>>>0,
				b=chk[cca](4)*16777216+chk[cca](5)*65536+chk[cca](6)*256+chk[cca](7)>>>0,c;
			c=_des.IP([a,b]); a=c[0]; b=c[1];
			for(var i=0;i<16;i++) {
				c=b; b=(feistel(b,k[dir?i:15-i])^a)>>>0; a=c;
			}
			c=_des.iIP([b,a]); a=c[0]; b=c[1];
			return chr(a>>24&255)+chr(a>>16&255)+chr(a>>8&255)+chr(a&255)+chr(b>>24&255)+chr(b>>16&255)+chr(b>>8&255)+chr(b&255);
		}
		function genkey(k) {
			var a=k[cca](0)*16777216+k[cca](1)*65536+k[cca](2)*256+k[cca](3)>>>0,
				b=k[cca](4)*16777216+k[cca](5)*65536+k[cca](6)*256+k[cca](7)>>>0;
			var c=_des.PC1_C([a,b]),d=_des.PC1_D([a,b]);
			
			var key=[];
			for(var i=0;i<16;i++) {
				c=rot28(c,_des.SH[i]);
				d=rot28(d,_des.SH[i]);
				key.push(_des.PC2([c>>>4,(((c&15)<<28)|d)>>>0]));
			}
			return key;
		}
		
		function genhash(msg,key,bcm,mode) {
			if(!(bcm instanceof t.bcmode)) bcm=defbcm;
			if(typeof key!="string") key="";
			var k;
			if(triple) {
				if(key.length<24) key+=strrep("\0",24-key.length);
				k=[genkey(key.slice(0,8)),genkey(key.slice(8,16)),genkey(key.slice(16,24))];
			} else {
				if(key.length<8) key+=strrep("\0",8-key.length);
				k=genkey(key);
			}
			
			var reqs=bcm.prepare(mode);
			if(!reqs.stream) msg+=strrep("\0",8-(msg.length-1)%8-1);
			
			var f=reqs.enc ?
				function enc(chk) {
					if(triple) return cipher(cipher(cipher(chk,k[0],true),k[1],false),k[2],true);
					return cipher(chk,k,true);
				} :
				function dec(chk) {
					if(triple) return cipher(cipher(cipher(chk,k[0],false),k[1],true),k[2],false);
					return cipher(chk,k,false);
				};
			
			return bcm.run(f,reqs,msg,8);
		}
		
		tt.to = function(msg,key,bcm) {
			return genhash(msg,key,bcm,true);
		}
		tt.from = function(msg,key,bcm) {
			return genhash(msg,key,bcm,false);
		}
	}
	var des=new t.des();
	t.des.to=des.to; t.des.from=des.from;
})(window);