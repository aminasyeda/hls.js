/**
 * highly optimized TS demuxer:
 * parse PAT, PMT
 * extract PES packet from audio and video PIDs
 * extract AVC/H264 NAL units and AAC/ADTS samples from PES packet
 * trigger the remuxer upon parsing completion
 * it also tries to workaround as best as it can audio codec switch (HE-AAC to AAC and vice versa), without having to restart the MediaSource.
 * it also controls the remuxing process :
 * upon discontinuity or level switch detection, it will also notifies the remuxer so that it can reset its state.
*/

 import * as ADTS from './adts';
 import MpegAudio from './mpegaudio';
 import Event from '../events';
 import ExpGolomb from './exp-golomb';
 import HEVCSpsParser from './hevc-sps-parser';
// import Hex from '../utils/hex';
 import {logger} from '../utils/logger';
 import {ErrorTypes, ErrorDetails} from '../errors';

// We are using fixed track IDs for driving the MP4 remuxer
// instead of following the TS PIDs.
// There is no reason not to do this and some browsers/SourceBuffer-demuxers
// may not like if there are TrackID "switches"
// See https://github.com/video-dev/hls.js/issues/1331
// Here we are mapping our internal track types to constant MP4 track IDs
// With MSE currently one can only have one track of each, and we are muxing
// whatever video/audio rendition in them.
const RemuxerTrackIdConfig = {
  video: 0,
  audio: 1,
  id3: 2,
  text: 3
};

class TSDemuxer {

  constructor(observer, remuxer, config, typeSupported) {
    this.observer = observer;
    this.config = config;
    this.lastCC = 0;
    this.remuxer = new this.remuxerClass(observer, id, config);
    this.HEVC = 0x24;
    this.AVC = 0x1b;
  }

  setDecryptData(decryptdata) {
    if ((decryptdata != null) && (decryptdata.key != null) && (decryptdata.method === 'SAMPLE-AES')) {
      this.sampleAes = new SampleAesDecrypter(this.observer, this.config, decryptdata, this.discardEPB);
    } else {
      this.sampleAes = null;
    }
  }

  static probe(data) {
    const syncOffset = TSDemuxer._syncOffset(data);
    if (syncOffset < 0)  {
      return false;
    } else {
      if (syncOffset) {
        logger.warn(`MPEG2-TS detected but first sync word found @ offset ${syncOffset}, junk ahead ?`);
      }
      return true;
    }
  }

  static _syncOffset(data) {
    // scan 1000 first bytes
    const scanwindow  = Math.min(1000,data.length - 3*188);
    let i = 0;
    while(i < scanwindow) {
      // a TS fragment should contain at least 3 TS packets, a PAT, a PMT, and one PID, each starting with 0x47
      if (data[i] === 0x47 && data[i+188] === 0x47 && data[i+2*188] === 0x47) {
        return i;
      } else {
        i++;
      }
    }
    return -1;
  }

  /**
   * Creates a track model internal to demuxer used to drive remuxing input
   *
   * @param {string} type 'audio' | 'video' | 'id3' | 'text'
   * @param {number} duration
   * @return {object} TSDemuxer's internal track model
   */
  static createTrack(type, duration) {
    return {
      container: type === 'video' || type === 'audio' ? 'video/mp2t' : undefined, 
      type, 
      id: RemuxerTrackIdConfig[type],
      pid : -1,
      inputTimeScale : 90000,
      sequenceNumber: 0,
      samples : [],
      len : 0,
      dropped : type === 'video' ? 0 : undefined,
      isAAC: type === 'audio' ? true : undefined,
      duration: type === 'audio' ? duration : undefined
    };
  }

  /**
   * Initializes a new init segment on the demuxer/remuxer interface. Needed for discontinuities/track-switches (or at stream start) 
   * Resets all internal track instances of the demuxer.
   *
   * @override Implements generic demuxing/remuxing interface (see DemuxerInline)
   * @param {object} initSegment
   * @param {string} audioCodec
   * @param {string} videoCodec
   * @param {number} duration (in TS timescale = 90kHz)
   */
  resetInitSegment(initSegment, audioCodec, videoCodec, duration) {
    this.pmtParsed = false;
    this._pmtId = -1;
    // codec HEVC = 0x24, AVC = 0x1b
    this._videoTrack = {container : 'video/mp2t', type: 'video', streamType: -1, PID : -1, sequenceNumber: 0, samples : [], len : 0, nbNalu : 0, dropped : 0};
    this._aacTrack = {container : 'video/mp2t', type: 'audio', id :-1, sequenceNumber: 0, samples : [], len : 0};
    this._id3Track = {type: 'id3', id :-1, sequenceNumber: 0, samples : [], len : 0};
    this._txtTrack = {type: 'text', id: -1, sequenceNumber: 0, samples: [], len: 0};
    // flush any partial content
    this.aacOverFlow = null;
    this.aacLastPTS = null;
    this.avcSample = null;
    this.audioCodec = audioCodec;
    this.videoCodec = videoCodec;
    this._duration = duration;
  }

  /**
   * 
   * @override
   */
  resetTimeStamp() {}

  // feed incoming data to the front of the parsing pipeline
  push(data, audioCodec, videoCodec, timeOffset, cc, level, sn, duration) {
    var videoData, aacData, id3Data,
        start, len = data.length, stt, pid, atf, offset,
        codecsOnly = this.remuxer.passthrough,
        unknownPIDs = false;
    this.contiguous = contiguous;
    var pmtParsed = this.pmtParsed,
        videoPID = this._videoTrack.PID,
        videoStreamType = this._videoTrack.streamType,
        aacId = this._aacTrack.id,
        id3Id = this._id3Track.id,
        pmtId = this._pmtId;

    var parsePAT = this._parsePAT,
        parsePMT = this._parsePMT,
        parsePES = this._parsePES,
        parseHEVCPES = this._parseHEVCPES.bind(this),
        parseAVCPES = this._parseAVCPES.bind(this),
        parseAACPES = this._parseAACPES.bind(this),
        parseMPEGPES = this._parseMPEGPES.bind(this),
        parseID3PES  = this._parseID3PES.bind(this);

    const syncOffset = TSDemuxer._syncOffset(data);

    // don't parse last TS packet if incomplete
    len -= (len + syncOffset) % 188;

    // loop through TS packets
    for (start = syncOffset; start < len; start += 188) {
      if (data[start] === 0x47) {
        stt = !!(data[start + 1] & 0x40);
        // pid is a 13-bit field starting at the last bit of TS[1]
        pid = ((data[start + 1] & 0x1f) << 8) + data[start + 2];
        atf = (data[start + 3] & 0x30) >> 4;
        // if an adaption field is present, its length is specified by the fifth byte of the TS packet header.
        if (atf > 1) {
          offset = start + 5 + data[start + 4];
          // continue if there is only adaptation field
          if (offset === (start + 188)) {
            continue;
          }
        } else {
          offset = start + 4;
        }
        switch(pid) {
          case videoPID:
            if (stt) {
              if (videoData) {
                var pesData = parsePES(videoData);
                if(videoStreamType === this.HEVC) {
                  parseHEVCPES(pesData);
                } 
                else if(videoStreamType === this.AVC) {
                  parseAVCPES(pesData);
                }
                else {
                  logger.error('unsupported video stream type'); 
                  return;
                }
                
                if (codecsOnly) {
                  // if we have video codec info AND
                  // if audio PID is undefined OR if we have audio codec info,
                  // we have all codec info !
                  if (this._videoTrack.codec && (aacId === -1 || this._aacTrack.codec)) {
                    this.remux(level,sn,data);
                    return;
                  }
                }
              }
              videoData = {data: [], size: 0};
            }
            if (videoData) {
              videoData.data.push(data.subarray(offset, start + 188));
              videoData.size += start + 188 - offset;
            }
            break;
          case audioId:
            if (stt) {
              if (aacData) {
                parseAACPES(parsePES(aacData));
                if (codecsOnly) {
                  // here we now that we have audio codec info
                  // if video PID is undefined OR if we have video codec info,
                  // we have all codec infos !
                  if (this._aacTrack.codec && (videoPID === -1 || this._videoTrack.codec)) {
                    this.remux(level,sn,data);
                    return;
                  }
                }
              }
              audioData = {data: [], size: 0};
            }
            if (audioData) {
              audioData.data.push(data.subarray(offset, start + 188));
              audioData.size += start + 188 - offset;
            }
            break;
          case id3Id:
            if (stt) {
              if (id3Data && (pes = parsePES(id3Data))) {
                parseID3PES(pes);
              }
              id3Data = {data: [], size: 0};
            }
            if (id3Data) {
              id3Data.data.push(data.subarray(offset, start + 188));
              id3Data.size += start + 188 - offset;
            }
            break;
          case 0:
            if (stt) {
              offset += data[offset] + 1;
            }
            pmtId = this._pmtId = parsePAT(data, offset);
            break;
          case pmtId:
            if (stt) {
              offset += data[offset] + 1;
            }
            let parsedPIDs = parsePMT(data, offset);
            videoPID = this._videoTrack.PID = parsedPIDs.videoPID;
            videoStreamType = this._videoTrack.streamType = parsedPIDs.videoStreamType;
            aacId = this._aacTrack.id = parsedPIDs.aac;
            id3Id = this._id3Track.id = parsedPIDs.id3;
            if (unknownPIDs && !pmtParsed) {
              logger.log('reparse from beginning');
              unknownPIDs = false;
              // we set it to -188, the += 188 in the for loop will reset start to 0
              start = syncOffset-188;
            }
            pmtParsed = this.pmtParsed = true;
            break;
          case 17:
          case 0x1fff:
            break;
          default:
            unknownPIDs = true;
            break;
        }
      } else {
        this.observer.trigger(Event.ERROR, {type : ErrorTypes.MEDIA_ERROR, details: ErrorDetails.FRAG_PARSING_ERROR, fatal: false, reason: 'TS packet did not start with 0x47'});
      }
    }
    // parse last PES packet
    if (videoData) {
      var pes = parsePES(videoData);
      if(videoStreamType === this.HEVC) {
        parseHEVCPES(pes);
      } 
      else if(videoStreamType === this.AVC) {
        parseAVCPES(pes);
      }
      else {
        logger.error('unsupported video stream type ' + videoStreamType); 
      }
    }

    if (id3Data && (pes = parsePES(id3Data))) {
      parseID3PES(pes);
      id3Track.pesData = null;
    } else {
      // either id3Data null or PES truncated, keep it for next frag parsing
      id3Track.pesData = id3Data;
    }

    if (this.sampleAes == null) {
      this.remuxer.remux(audioTrack, avcTrack, id3Track, this._txtTrack, timeOffset, contiguous, accurateTimeOffset);
    } else {
      this.decryptAndRemux(audioTrack, avcTrack, id3Track, this._txtTrack, timeOffset, contiguous, accurateTimeOffset);
    }
  }

  remux(level, sn, data) {
    this.remuxer.remux(level, sn, this._aacTrack, this._videoTrack, this._id3Track, this._txtTrack, this.timeOffset, this.contiguous, data);
  }

  destroy() {
    this._initPTS = this._initDTS = undefined;
    this._duration = 0;
  }

  _parsePAT(data, offset) {
    // skip the PSI header and parse the first PMT entry
    return (data[offset + 10] & 0x1F) << 8 | data[offset + 11];
    //logger.log('PMT PID:'  + this._pmtId);
  }

  _parsePMT(data, offset) {
    var sectionLength, tableEnd, programInfoLength, pid, result = { aac : -1, videoPID : -1, videoStreamType: -1, id3 : -1};
    sectionLength = (data[offset + 1] & 0x0f) << 8 | data[offset + 2];
    tableEnd = offset + 3 + sectionLength - 4;
    // to determine where the table is, we have to figure out how
    // long the program info descriptors are
    programInfoLength = (data[offset + 10] & 0x0f) << 8 | data[offset + 11];
    // advance the offset to the first entry in the mapping table
    offset += 12 + programInfoLength;
    while (offset < tableEnd) {
      pid = (data[offset + 1] & 0x1F) << 8 | data[offset + 2];
      var streamType  = data[offset];
      switch(streamType) {
        // ISO/IEC 13818-7 ADTS AAC (MPEG-2 lower bit-rate audio)
        case 0x0f:
          //logger.log('AAC PID:'  + pid);
          if (result.audio === -1) {
            result.audio = pid;
          }
          break;

        // Packetized metadata (ID3)
        case 0x15:
          //logger.log('ID3 PID:'  + pid);
          if (result.id3 === -1) {
            result.id3 = pid;
          }
          break;
        // HEVC
        case 0x24:
          if (result.videoPID === -1) {
            result.videoPID = pid;
            result.videoStreamType = streamType;
          }
          break;
        // ITU-T Rec. H.264 and ISO/IEC 14496-10 (lower bit-rate video)
        case 0x1b:
          if (result.videoPID === -1) {
            result.videoPID = pid;
            result.videoStreamType = streamType;
          }
          break;

        default:
        logger.log('unkown stream type:'  + streamType);
        break;
      }
      // move to the next table entry
      // skip past the elementary stream descriptors, if present
      offset += ((data[offset + 3] & 0x0F) << 8 | data[offset + 4]) + 5;
    }
    return result;
  }

  _parsePES(stream) {
    var i = 0, frag, pesFlags, pesPrefix, pesLen, pesHdrLen, pesData, pesPts, pesDts, payloadStartOffset, data = stream.data;
    // safety check
    if (!stream || stream.size === 0) {
      return null;
    }

    // we might need up to 19 bytes to read PES header
    // if first chunk of data is less than 19 bytes, let's merge it with following ones until we get 19 bytes
    // usually only one merge is needed (and this is rare ...)
    while(data[0].length < 19 && data.length > 1) {
      let newData = new Uint8Array(data[0].length + data[1].length);
      newData.set(data[0]);
      newData.set(data[1], data[0].length);
      data[0] = newData;
      data.splice(1,1);
    }
    //retrieve PTS/DTS from first fragment
    frag = data[0];
    pesPrefix = (frag[0] << 16) + (frag[1] << 8) + frag[2];
    if (pesPrefix === 1) {
      pesLen = (frag[4] << 8) + frag[5];
      // if PES parsed length is not zero and greater than total received length, stop parsing. PES might be truncated
      // minus 6 : PES header size
      if (pesLen && pesLen > stream.size - 6) {
        return null;
      }
      pesFlags = frag[7];
      if (pesFlags & 0xC0) {
        /* PES header described here : http://dvd.sourceforge.net/dvdinfo/pes-hdr.html
            as PTS / DTS is 33 bit we cannot use bitwise operator in JS,
            as Bitwise operators treat their operands as a sequence of 32 bits */
        pesPts = (frag[9] & 0x0E) * 536870912 +// 1 << 29
          (frag[10] & 0xFF) * 4194304 +// 1 << 22
          (frag[11] & 0xFE) * 16384 +// 1 << 14
          (frag[12] & 0xFF) * 128 +// 1 << 7
          (frag[13] & 0xFE) / 2;
          // check if greater than 2^32 -1
          if (pesPts > 4294967295) {
            // decrement 2^33
            pesPts -= 8589934592;
          }
        if (pesFlags & 0x40) {
          pesDts = (frag[14] & 0x0E ) * 536870912 +// 1 << 29
            (frag[15] & 0xFF ) * 4194304 +// 1 << 22
            (frag[16] & 0xFE ) * 16384 +// 1 << 14
            (frag[17] & 0xFF ) * 128 +// 1 << 7
            (frag[18] & 0xFE ) / 2;
          // check if greater than 2^32 -1
          if (pesDts > 4294967295) {
            // decrement 2^33
            pesDts -= 8589934592;
          }
          if (pesPts - pesDts > 60*90000) {
            logger.warn(`${Math.round((pesPts - pesDts)/90000)}s delta between PTS and DTS, align them`);
            pesPts = pesDts;
          }
        } else {
          pesDts = pesPts;
        }
      }
      pesHdrLen = frag[8];
      // 9 bytes : 6 bytes for PES header + 3 bytes for PES extension
      payloadStartOffset = pesHdrLen + 9;

      stream.size -= payloadStartOffset;
      //reassemble PES packet
      pesData = new Uint8Array(stream.size);
      for( let j = 0, dataLen = data.length; j < dataLen ; j++) {
        frag = data[j];
        let len = frag.byteLength;
        if (payloadStartOffset) {
          if (payloadStartOffset > len) {
            // trim full frag if PES header bigger than frag
            payloadStartOffset-=len;
            continue;
          } else {
            // trim partial frag if PES header smaller than frag
            frag = frag.subarray(payloadStartOffset);
            len-=payloadStartOffset;
            payloadStartOffset = 0;
          }
        }
        pesData.set(frag, i);
        i+=len;
      }
      if (pesLen) {
        // payload size : remove PES header + PES extension
        pesLen -= pesHdrLen+3;
      }
      return {data: pesData, pts: pesPts, dts: pesDts, len: pesLen};
    } else {
      return null;
    }
  }

  _parseHEVCPES(pes) {
        var track = this._videoTrack,
        samples = track.samples,
        units = this._parseHEVCNALu(pes.data),
        units2 = [],
        debug = false,
        key = false,
        length = 0,
        // expGolombDecoder,
        avcSample,
        push;
        // i;
    // no NALu found
    if (units.length === 0 && samples.length > 0) {
      // append pes.data to previous NAL unit
      var lastavcSample = samples[samples.length - 1];
      var lastUnit = lastavcSample.units.units[lastavcSample.units.units.length - 1];
      var tmp = new Uint8Array(lastUnit.data.byteLength + pes.data.byteLength);
      tmp.set(lastUnit.data, 0);
      tmp.set(pes.data, lastUnit.data.byteLength);
      lastUnit.data = tmp;
      lastavcSample.units.length += pes.data.byteLength;
      track.len += pes.data.byteLength;
    }
    //free pes.data to save up some memory
    pes.data = null;
    var debugString = '';

    var pushAccesUnit = function() {
      if (units2.length) {
        // only push AVC sample if starting with a keyframe is not mandatory OR
        //    if keyframe already found in this fragment OR
        //       keyframe found in last fragment (track.sps) AND
        //          samples already appended (we already found a keyframe in this fragment) OR fragment is contiguous
        if (!this.config.forceKeyFrameOnDiscontinuity ||
            key === true ||
            (track.sps /*&& (samples.length || this.contiguous)*/)) 
        {
          avcSample = {units: { units : units2, length : length}, pts: pes.pts, dts: pes.dts, key: key};
          samples.push(avcSample);
          track.len += length;
          track.nbNalu += units2.length;
        } else {
          // dropped samples, track it
          track.dropped++;
        }
        units2 = [];
        length = 0;
      }
    }.bind(this);

    units.forEach(unit => {
      switch(unit.type) {
        case 0:
          push = true;
          if(debug) {
            debugString += 'SLICE_TRAIL_N ';
          }
          break;
        case 1:
          push = true;
          if(debug) {
            debugString += 'SLICE_TRAIL_R ';
          }
          key = true;
          break;
        case 2:
          push = true;
           if(debug) {
            debugString += 'SLICE_TSA_N ';
          }
          break;
        case 3:
          push = true;
          if(debug) {
            debugString += 'SLICE_TSA_R ';
          }
          key = true;
          break;
        case 4:
          push = true;
          if(debug) {
            debugString += 'SLICE_STSA_N ';
          }
          break;
        case 5:
          push = true;
          if(debug) {
            debugString += 'SLICE_STSA_R ';
          }
          key = true;
          break;
        case 6:
          push = true;
          if(debug) {
            debugString += 'SLICE_RADL_N ';
          }
          break;
        case 7:
          push = true;
          if(debug) {
            debugString += 'SLICE_RADL_R ';
          }
          key = true;
          break;
        case 8:
          push = true;
          if(debug) {
            debugString += 'SLICE_RASL_N ';
          }
          break;                                                  
        case 9:
          push = true;
          if(debug) {
            debugString += 'SLICE_RASL_R ';
          }
          key = true;
          break; 
        case 16:
          push = true;
          if(debug) {
            debugString += 'SLICE_BLA_W_LP ';
          }
          break; 
        case 17:
          push = true;
          if(debug) {
            debugString += 'SLICE_BLA_W_RADL ';
          }
          break;   
        case 18:
          push = true;
          if(debug) {
            debugString += 'SLICE_BLA_N_LP ';
          }
          break; 
        case 19:
          push = true;
          if(debug) {
            debugString += 'SLICE_IDR_W_RADL ';
          }
          key = true;
          break;   
        case 20:
          push = true;
          if(debug) {
            debugString += 'SLICE_IDR_N_LP ';
          }
          key = true;
          break; 
        case 21:
          push = true;
          if(debug) {
            debugString += 'SLICE_CRA_NUT ';
          }
          key = true;
          break;
        case 32:
          push = true;
          track.vps = [unit.data];
          if(debug) {
            debugString += 'VPS ';
          }
          break;           
        //SPS
        case 33:
          push = true;
          if(debug) {
            debugString += 'SPS ';
          }
          track.sps = [unit.data];

          var hevcSPSParser = new HEVCSpsParser(unit.data);
          var config = hevcSPSParser.readSPSHEVC();
          track.width = config.width;
          track.height = config.height;
          track.duration = this._duration;
          track.codec = 'hev1.1.6.L93.B0';
          track.chromaFormatIdc = config.chromaFormatIdc;
          track.bitDepthLumaMinus8 = config.bitDepthLumaMinus8;
          track.bitDepthChromaMinus8 = config.bitDepthChromaMinus8;
          break;
        //PPS
        case 34:
          push = true;
          if(debug) {
            debugString += 'PPS ';
          }
          // if (!track.pps) {
            track.pps = [unit.data];
          // }
          break;
        case 35:
          push = false;
          if(debug) {
            debugString += 'AUD ';
          }
          pushAccesUnit();
          break;
        case 36:
          push = true;
          if(debug) {
            debugString += 'EOS ';
          }
          break;
        case 37:
          push = true;
          if(debug) {
            debugString += 'EOB ';
          }
          break;          
        case 38:
          push = true;
          if(debug) {
            debugString += 'FD ';
          }
          break;          
        case 39:
          push = true;
          if(debug) {
            debugString += 'PREFIX_SEI ';
          }
          break;          
        case 40:
          push = true;
          if(debug) {
            debugString += 'SUFFIX_SEI ';
          }
          break;           
        default:
          push = false;
          debugString += 'unknown NAL ' + unit.type + ' ';
          break;
      }
      if(push) {
        units2.push(unit);
        length+=unit.data.byteLength;
      }
    });
    if(debug || debugString.length) {
      logger.log(debugString);
    }
    pushAccesUnit();
  }

  _parseAVCPES(pes) {
    var track = this._videoTrack,
        samples = track.samples,
        units = this._parseAVCNALu(pes.data),
        debug = false,
        expGolombDecoder,
        avcSample = this.avcSample,
        push,
        spsfound = false,
        i,
        pushAccesUnit = this.pushAccesUnit.bind(this),
        createAVCSample = function(key,pts,dts,debug) {
          return { key : key, pts : pts, dts : dts, units : [], debug : debug};
        };
    //free pes.data to save up some memory
    pes.data = null;

    // if new NAL units found and last sample still there, let's push ...
    // this helps parsing streams with missing AUD (only do this if AUD never found)
    if (avcSample && units.length && !track.audFound) {
      pushAccesUnit(avcSample,track);
      avcSample = this.avcSample = createAVCSample(false,pes.pts,pes.dts,'');
    }

    units.forEach(unit => {
      switch(unit.type) {
        //NDR
         case 1:
           push = true;
           if (!avcSample) {
            avcSample = this.avcSample = createAVCSample(true,pes.pts,pes.dts,'');
           }
           if(debug) {
            avcSample.debug += 'NDR ';
           }
           avcSample.frame = true;
           let data = unit.data;
           // only check slice type to detect KF in case SPS found in same packet (any keyframe is preceded by SPS ...)
           if (spsfound && data.length > 4) {
             // retrieve slice type by parsing beginning of NAL unit (follow H264 spec, slice_header definition) to detect keyframe embedded in NDR
             let sliceType = new ExpGolomb(data).readSliceType();
             // 2 : I slice, 4 : SI slice, 7 : I slice, 9: SI slice
             // SI slice : A slice that is coded using intra prediction only and using quantisation of the prediction samples.
             // An SI slice can be coded such that its decoded samples can be constructed identically to an SP slice.
             // I slice: A slice that is not an SI slice that is decoded using intra prediction only.
             //if (sliceType === 2 || sliceType === 7) {
             if (sliceType === 2 || sliceType === 4 || sliceType === 7 || sliceType === 9) {
                avcSample.key = true;
             }
           }
           break;
        //IDR
        case 5:
          push = true;
          // handle PES not starting with AUD
          if (!avcSample) {
            avcSample = this.avcSample = createAVCSample(true,pes.pts,pes.dts,'');
          }
          if(debug) {
            avcSample.debug += 'IDR ';
          }
          avcSample.key = true;
          avcSample.frame = true;
          break;
        //SEI
        case 6:
          push = true;
          if(debug && avcSample) {
            avcSample.debug += 'SEI ';
          }
          expGolombDecoder = new ExpGolomb(this.discardEPB(unit.data));

          // skip frameType
          expGolombDecoder.readUByte();

          var payloadType = 0;
          var payloadSize = 0;
          var endOfCaptions = false;
          var b = 0;

          while (!endOfCaptions && expGolombDecoder.bytesAvailable > 1) {
            payloadType = 0;
            do {
                b = expGolombDecoder.readUByte();
                payloadType += b;
            } while (b === 0xFF);

            // Parse payload size.
            payloadSize = 0;
            do {
                b = expGolombDecoder.readUByte();
                payloadSize += b;
            } while (b === 0xFF);

            // TODO: there can be more than one payload in an SEI packet...
            // TODO: need to read type and size in a while loop to get them all
            if (payloadType === 4 && expGolombDecoder.bytesAvailable !== 0) {

              endOfCaptions = true;

              var countryCode = expGolombDecoder.readUByte();

              if (countryCode === 181) {
                var providerCode = expGolombDecoder.readUShort();

                if (providerCode === 49) {
                  var userStructure = expGolombDecoder.readUInt();

                  if (userStructure === 0x47413934) {
                    var userDataType = expGolombDecoder.readUByte();

                    // Raw CEA-608 bytes wrapped in CEA-708 packet
                    if (userDataType === 3) {
                      var firstByte = expGolombDecoder.readUByte();
                      var secondByte = expGolombDecoder.readUByte();

                      var totalCCs = 31 & firstByte;
                      var byteArray = [firstByte, secondByte];

                      for (i = 0; i < totalCCs; i++) {
                        // 3 bytes per CC
                        byteArray.push(expGolombDecoder.readUByte());
                        byteArray.push(expGolombDecoder.readUByte());
                        byteArray.push(expGolombDecoder.readUByte());
                      }

                      this._insertSampleInOrder(this._txtTrack.samples, { type: 3, pts: pes.pts, bytes: byteArray });
                    }
                  }
                }
              }
            }
            else if (payloadSize < expGolombDecoder.bytesAvailable)
            {
              for (i = 0; i<payloadSize; i++)
              {
                expGolombDecoder.readUByte();
              }
            }
          }
          break;
        //SPS
        case 7:
          push = true;
          spsfound = true;
          if(debug && avcSample) {
            avcSample.debug += 'SPS ';
          }
          if(!track.sps) {
            expGolombDecoder = new ExpGolomb(unit.data);
            var config = expGolombDecoder.readSPS();
            track.width = config.width;
            track.height = config.height;
            track.pixelRatio = config.pixelRatio;
            track.sps = [unit.data];
            track.duration = this._duration;
            var codecarray = unit.data.subarray(1, 4);
            var codecstring = 'avc1.';
            for (i = 0; i < 3; i++) {
              var h = codecarray[i].toString(16);
              if (h.length < 2) {
                h = '0' + h;
              }
              codecstring += h;
            }
            track.codec = codecstring;
          }
          break;
        //PPS
        case 8:
          push = true;
          if(debug && avcSample) {
            avcSample.debug += 'PPS ';
          }
          if (!track.pps) {
            track.pps = [unit.data];
          }
          break;
        // AUD
        case 9:
          push = false;
          track.audFound = true;
          if (avcSample) {
            pushAccesUnit(avcSample,track);
          }
          avcSample = this.avcSample = createAVCSample(false,pes.pts,pes.dts,debug ? 'AUD ': '');
          break;
        // Filler Data
        case 12:
          push = false;
          break;
        default:
          push = false;
          if (avcSample) {
            avcSample.debug += 'unknown NAL ' + unit.type + ' ';
          }
          break;
      }
      if(avcSample && push) {
        let units = avcSample.units;
        units.push(unit);
      }
    });
    // if last PES packet, push samples
    if (last && avcSample) {
      pushAccesUnit(avcSample,track);
      this.avcSample = null;
    }
  }

  _insertSampleInOrder(arr, data) {
    var len = arr.length;
    if (len > 0) {
      if (data.pts >= arr[len-1].pts)
      {
        arr.push(data);
      }
      else {
        for (var pos = len - 1; pos >= 0; pos--) {
          if (data.pts < arr[pos].pts) {
            arr.splice(pos, 0, data);
            break;
          }
        }
      }
    }
    else {
      arr.push(data);
    }
  }

  _parseHEVCNALu(array) {
    var i = 0, len = array.byteLength, value, overflow, state = this.avcNaluState;
    var units = [], unit, unitType, lastUnitStart, lastUnitType;
    //logger.log('PES:' + Hex.hexDump(array));
    while (i < len) {
      value = array[i++];
      // finding 3 or 4-byte start codes (00 00 01 OR 00 00 00 01)
      switch (state) {
        case 0:
          if (value === 0) {
            state = 1;
          }
          break;
        case 1:
          if( value === 0) {
            state = 2;
          } else {
            state = 0;
          }
          break;
        case 2:
        case 3:
          if( value === 0) {
            state = 3;
          } else if (value === 1 && i < len) {
            unitType = (array[i] >>> 1) & 0x3F;
            logger.log('find NALU @ offset:' + i + ',type:' + unitType);
            if (lastUnitStart) {
              unit = {data: array.subarray(lastUnitStart, i - state - 1), type: lastUnitType};
              //logger.log('pushing NALU, type/size:' + unit.type + '/' + unit.data.byteLength);
              units.push(unit);
            } else {
              // lastUnitStart is undefined => this is the first start code found in this PES packet
              // first check if start code delimiter is overlapping between 2 PES packets,
              // ie it started in last packet (lastState not zero)
              // and ended at the beginning of this PES packet (i <= 4 - lastState)
              let lastState = this.avcNaluState;
              if(lastState &&  (i <= 4 - lastState)) {
                // start delimiter overlapping between PES packets
                // strip start delimiter bytes from the end of last NAL unit
                let track = this._videoTrack,
                    samples = track.samples;
                if (samples.length) {
                  let lastavcSample = samples[samples.length - 1],
                      lastUnits = lastavcSample.units.units,
                      lastUnit = lastUnits[lastUnits.length - 1];
                  // check if lastUnit had a state different from zero
                  if (lastUnit.state) {
                    // strip last bytes
                    lastUnit.data = lastUnit.data.subarray(0,lastUnit.data.byteLength - lastState);
                    lastavcSample.units.length -= lastState;
                    track.len -= lastState;
                  }
                }
              }
              // If NAL units are not starting right at the beginning of the PES packet, push preceding data into previous NAL unit.
              overflow  = i - state - 1;
              if (overflow > 0) {
                let track = this._avcTrack,
                    samples = track.samples;
                //logger.log('first NALU found with overflow:' + overflow);
                if (samples.length) {
                  let lastavcSample = samples[samples.length - 1],
                      lastUnits = lastavcSample.units.units,
                      lastUnit = lastUnits[lastUnits.length - 1],
                      tmp = new Uint8Array(lastUnit.data.byteLength + overflow);
                  tmp.set(lastUnit.data, 0);
                  tmp.set(array.subarray(0, overflow), lastUnit.data.byteLength);
                  lastUnit.data = tmp;
                  lastavcSample.units.length += overflow;
                  track.len += overflow;
                }
              }
            }
            lastUnitStart = i;
            lastUnitType = unitType;
            state = 0;
          } else {
            state = 0;
          }
          break;
        default:
          break;
      }
    }
    if (lastUnitStart) {
      unit = {data: array.subarray(lastUnitStart, len), type: lastUnitType, state : state};
      units.push(unit);
      //logger.log('pushing NALU, type/size/state:' + unit.type + '/' + unit.data.byteLength + '/' + state);
      this.avcNaluState = state;
    }
    return units;
  }

  _parseAVCNALu(array) {
    var i = 0, len = array.byteLength, value, overflow, track = this._avcTrack, state = track.naluState || 0, lastState = state;
    var units = [], unit, unitType, lastUnitStart = -1, lastUnitType;
    //logger.log('PES:' + Hex.hexDump(array));

    if (state === -1) {
    // special use case where we found 3 or 4-byte start codes exactly at the end of previous PES packet
      lastUnitStart = 0;
      // NALu type is value read from offset 0
      lastUnitType = array[0] & 0x1f;
      state = 0;
      i = 1;
    }

    while (i < len) {
      value = array[i++];
      // optimization. state 0 and 1 are the predominant case. let's handle them outside of the switch/case
      if (!state) {
        state = value ? 0 : 1;
        continue;
      }
      if (state === 1) {
        state = value ? 0 : 2;
        continue;
      }
      // here we have state either equal to 2 or 3
      if(!value) {
        state = 3;
      } else if (value === 1) {
        if (lastUnitStart >=0) {
          unit = {data: array.subarray(lastUnitStart, i - state - 1), type: lastUnitType};
          //logger.log('pushing NALU, type/size:' + unit.type + '/' + unit.data.byteLength);
          units.push(unit);
        } else {
          // lastUnitStart is undefined => this is the first start code found in this PES packet
          // first check if start code delimiter is overlapping between 2 PES packets,
          // ie it started in last packet (lastState not zero)
          // and ended at the beginning of this PES packet (i <= 4 - lastState)
          let lastUnit = this._getLastNalUnit();
          if (lastUnit) {
            if(lastState &&  (i <= 4 - lastState)) {
              // start delimiter overlapping between PES packets
              // strip start delimiter bytes from the end of last NAL unit
                // check if lastUnit had a state different from zero
              if (lastUnit.state) {
                // strip last bytes
                lastUnit.data = lastUnit.data.subarray(0,lastUnit.data.byteLength - lastState);
              }
            }
            // If NAL units are not starting right at the beginning of the PES packet, push preceding data into previous NAL unit.
            overflow  = i - state - 1;
            if (overflow > 0) {
              //logger.log('first NALU found with overflow:' + overflow);
              let tmp = new Uint8Array(lastUnit.data.byteLength + overflow);
              tmp.set(lastUnit.data, 0);
              tmp.set(array.subarray(0, overflow), lastUnit.data.byteLength);
              lastUnit.data = tmp;
            }
          }
        }
        // check if we can read unit type
        if (i < len) {
          unitType = array[i] & 0x1f;
          //logger.log('find NALU @ offset:' + i + ',type:' + unitType);
          lastUnitStart = i;
          lastUnitType = unitType;
          state = 0;
        } else {
          // not enough byte to read unit type. let's read it on next PES parsing
          state = -1;
        }
      } else {
        state = 0;
      }
    }
    if (lastUnitStart >=0 && state >=0) {
      unit = {data: array.subarray(lastUnitStart, len), type: lastUnitType, state : state};
      units.push(unit);
      //logger.log('pushing NALU, type/size/state:' + unit.type + '/' + unit.data.byteLength + '/' + state);
    }
    // no NALu found
    if (units.length === 0) {
      // append pes.data to previous NAL unit
      let  lastUnit = this._getLastNalUnit();
      if (lastUnit) {
        let tmp = new Uint8Array(lastUnit.data.byteLength + array.byteLength);
        tmp.set(lastUnit.data, 0);
        tmp.set(array, lastUnit.data.byteLength);
        lastUnit.data = tmp;
      }
    }
    track.naluState = state;
    return units;
  }

  /**
   * remove Emulation Prevention bytes from a RBSP
   */
  discardEPB(data) {
    var length = data.byteLength,
        EPBPositions = [],
        i = 1,
        newLength, newData;

    // Find all `Emulation Prevention Bytes`
    while (i < length - 2) {
      if (data[i] === 0 &&
          data[i + 1] === 0 &&
          data[i + 2] === 0x03) {
        EPBPositions.push(i + 2);
        i += 2;
      } else {
        i++;
      }
    }

    // If no Emulation Prevention Bytes were found just return the original
    // array
    if (EPBPositions.length === 0) {
      return data;
    }

    // Create a new array to hold the NAL unit data
    newLength = length - EPBPositions.length;
    newData = new Uint8Array(newLength);
    var sourceIndex = 0;

    for (i = 0; i < newLength; sourceIndex++, i++) {
      if (sourceIndex === EPBPositions[0]) {
        // Skip this byte
        sourceIndex++;
        // Remove this position index
        EPBPositions.shift();
      }
      newData[i] = data[sourceIndex];
    }
    return newData;
  }

  _parseAACPES(pes) {
    var track = this._audioTrack,
        data = pes.data,
        pts = pes.pts,
        startOffset = 0,
        aacOverFlow = this.aacOverFlow,
        aacLastPTS = this.aacLastPTS,
        frameDuration, frameIndex, offset, stamp, len;
    if (aacOverFlow) {
      var tmp = new Uint8Array(aacOverFlow.byteLength + data.byteLength);
      tmp.set(aacOverFlow, 0);
      tmp.set(data, aacOverFlow.byteLength);
      //logger.log(`AAC: append overflowing ${aacOverFlow.byteLength} bytes to beginning of new PES`);
      data = tmp;
    }
    // look for ADTS header (0xFFFx)
    for (offset = startOffset, len = data.length; offset < len - 1; offset++) {
      if (ADTS.isHeader(data, offset)) {
        break;
      }
    }
    // if ADTS header does not start straight from the beginning of the PES payload, raise an error
    if (offset) {
      var reason, fatal;
      if (offset < len - 1) {
        reason = `AAC PES did not start with ADTS header,offset:${offset}`;
        fatal = false;
      } else {
        reason = 'no ADTS header found in AAC PES';
        fatal = true;
      }
      logger.warn(`parsing error:${reason}`);
      this.observer.trigger(Event.ERROR, {type: ErrorTypes.MEDIA_ERROR, details: ErrorDetails.FRAG_PARSING_ERROR, fatal: fatal, reason: reason});
      if (fatal) {
        return;
      }
    }

    ADTS.initTrackConfig(track, this.observer, data, offset, this.audioCodec);
    frameIndex = 0;
    frameDuration = ADTS.getFrameDuration(track.samplerate);

    // if last AAC frame is overflowing, we should ensure timestamps are contiguous:
    // first sample PTS should be equal to last sample PTS + frameDuration
    if(aacOverFlow && aacLastPTS) {
      var newPTS = aacLastPTS+frameDuration;
      if(Math.abs(newPTS-pts) > 1) {
        logger.log(`AAC: align PTS for overlapping frames by ${Math.round((newPTS-pts)/90)}`);
        pts=newPTS;
      }
    }

    //scan for aac samples
    while (offset < len) {
      if (ADTS.isHeader(data, offset) && (offset + 5) < len) {
        var frame = ADTS.appendFrame(track, data, offset, pts, frameIndex);
        if (frame) {
          //logger.log(`${Math.round(frame.sample.pts)} : AAC`);
          offset += frame.length;
          stamp = frame.sample.pts;
          frameIndex++;
        } else {
          //logger.log('Unable to parse AAC frame');
          break;
        }
      } else {
        //nothing found, keep looking
        offset++;
      }
    }

    if (offset < len) {
      aacOverFlow = data.subarray(offset, len);
      //logger.log(`AAC: overflow detected:${len-offset}`);
    } else {
      aacOverFlow = null;
    }
    this.aacOverFlow = aacOverFlow;
    this.aacLastPTS = stamp;
  }

  _parseMPEGPES(pes) {
    var data = pes.data;
    var length = data.length;
    var frameIndex = 0;
    var offset = 0;
    var pts = pes.pts;

    while (offset < length) {
      if (MpegAudio.isHeader(data, offset)) {
        var frame = MpegAudio.appendFrame(this._audioTrack, data, offset, pts, frameIndex);
        if (frame) {
          offset += frame.length;
          frameIndex++;
        } else {
          //logger.log('Unable to parse Mpeg audio frame');
          break;
        }
      } else {
        //nothing found, keep looking
        offset++;
      }
    }
  }

  _parseID3PES(pes) {
    this._id3Track.samples.push(pes);
  }
}

export default TSDemuxer;
