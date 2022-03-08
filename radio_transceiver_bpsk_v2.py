#############################################################################################################
# File:        FM_Transceiver.py - Using: GNU Radio version: 3.7.14.0
# Description: FM Walkie-Talkie using LimeSDR Transceiver 
#              ----------------------------------------------------------------------------------------------
# Notes      : Major, Minor and Revision notes:
#              ----------------------------------------------------------------------------------------------
#              Major    - Software major number will counting up each time there is a major changes on the 
#                         software features. Minor number will reset to '0' and revision number will reset
#                         to '1' (on each major changes). Initially major number will be set to '1'
#              Minor    - Software minor number will counting up each time there is a minor changes on the
#                         software. Revision number will reset to '1' (on each minor changes).
#              Revision - Software revision number will counting up each time there is a bug fixing on the
#                         on the current major and minor number.
#              ----------------------------------------------------------------------------------------------
#              Current Features & Bug Fixing Information
#              ----------------------------------------------------------------------------------------------
#              0001     - FM walkie-talkie transceiver with UHF frequency 446.094MHz using LimeSDR.
#              0002     - Transmitter and receiver processing are using gnuradio flow graph (.grc). So the
#                         first design radio process are done at gnuradio level by using gnuradio-companion
#                         application.
#              0003     - Generate radio transceiver block python script by using gnuradio-companion, then
#                         expand the script to include controlling process between transmitter and receiver.
#              0004     - Include PTT functionality to execute radio transmission to other radio. By default
#                         the transceiver are in receiving mode.
#              0005     - Include an indicator for both receiving mode and transmitter mode.
#              0006     - Add an embedded python block inside flow graph for audio detection functionality.
#                         Embedded python block are just a python script that we can include inside our flow
#                         graph to automatically detect the audio signal once after received the signal from 
#                         FM demodulator. Then this block will raised a flag to indicate the audio signal
#                         that already been detected. This daemon will read the current flag status inside 
#                         a dedicated thread and activate LED to indicate the radio received the clean
#                         audio signal.
#              0007     - Remove all variable related to transmit and receive mode all in one top block.
#              0008     - Implements one FM transceiver top block where this top block will call/connects to
#                         radio transmit and receive block based on hierarchical method. This method were used
#                         to make sure a transmit and receive block run concurrently.
#              0009     - Create an audio detection class (embedded python block) inside this main script. No
#                         need to import this class outside the main script. This is to ensure the process
#                         debugging can be implement within this main script easily.
#              0010     - Solve the script bug, where the script hang when PTT is pressed while radio still in 
#                         rx mode plus doing an audio detection process. Somehow the audio detection process
#                         block the script process from changing the radio to tx mode. Solved by delete a
#                         selector block logic and replace it by controlling and changing the radio tx frequency
#                         during script execution to allowed the transmit and receive process changeover without
#                         the two blocks (tx and rx block) disconnected.
#              0011     - Clean up unnecessary logic inside the main script (FM_Transceiver.py)
#              0012     - Add GPIO for antenna switcher control.
#
#              ----------------------------------------------------------------------------------------------
# Author : Ahmad Bahari Nizam B. Abu Bakar.
#
# Version: 1.0.1
# Version: 1.0.2 - Add feature item [0007,0008, 0009, 0010, 0011]. Please refer above description
# Version: 1.0.3 - Add feature item [0012]. Please refer above description
#
# Date   : 18/08/2020 (INITIAL RELEASE DATE)
# Date   : 12/09/2020 (INITIAL RELEASE DATE)
#
#############################################################################################################

from gnuradio import analog
from gnuradio import audio
from gnuradio import blocks
from gnuradio import digital
from gnuradio import eng_notation
from gnuradio import filter
from gnuradio import gr
from gnuradio.eng_option import eng_option
from gnuradio.filter import firdes
from gnuradio.filter import pfb
from grc_gnuradio import blks2 as grc_blks2
from optparse import OptionParser

from threading import Thread
from SocketServer import ThreadingMixIn

#import epy_block_0
import limesdr
import thread
import time
import logging
import logging.handlers
import os 
import sys
import socket
import numpy
import numpy as np

# Retrieve command comm configuration
from settings import localip
from settings import rxportno
from settings import txportno

# Retrieve current radio receiver configuration 
from settings import rxvolume
from settings import rxfreq
from settings import rxsmplrate
from settings import rxanabw
from settings import rxdigbw
from settings import rxgain
from settings import rxsquelch

# Retrieve current radio transmitter configuration
from settings import txfreq
from settings import txsmplrate
from settings import txanabw
from settings import txdigbw
from settings import txgain

# Retrieve current radio receiver configuration for digital modulation
from settings import digmodrxfreq
from settings import digmodrxsrate
from settings import digmodrxgain
from settings import digmodrxssrcsrate
from settings import digmodrxssrcfoff
from settings import digmodrxtcpip
from settings import digmodrxtcppno
from settings import digmodrxbw
from settings import digmodrxant
from settings import digmodrxcalib

# Retrieve current radio transmitter configuration for digital modulation
from settings import digmodtxfreq
from settings import digmodtxsrate
from settings import digmodtxgain
from settings import digmodtxssrcsrate
from settings import digmodtxssrcfoff
from settings import digmodtxtcpip
from settings import digmodtxtcppno
from settings import digmodtxbw
from settings import digmodtxant
from settings import digmodtxcalib

# Global variable declaration
backLogger                     = False       # Macro for logger
radioRxTx                      = False       # Radio transmit and receive flag
radioRxTxSysChk                = False       # Macro for radio receive-transmit check flag
raspiIO                        = False       # Macro for raspberry GPIO flag
rxRadioParamUpdt               = False       # Update status flag for receiver parameters retrieval
txRadioParamUpdt               = False       # Update status flag for transmitter parameters retrieval
voiceOperParamUpdt             = False       # Update status flag for radio voice operation parameters retrieval
pttStatusUpdt                  = 0           # Current PTT action flag
rxBlckVolUpdt                  = 0           # Update status flag for receiver audio volume
rxBlckCFreqUpdt                = 0           # Update status flag for receiver center frequency
rxBlckSmplRUpdt                = 0           # Update status flag for receiver sample rate
rxBlckBWUpdt                   = 0           # Update status flag for receiver analog filter BW
rxBlckDFiltUpdt                = 0           # Update status flag for receiver digital filter BW
rxBlckGainUpdt                 = 0           # Update status flag for receiver gain
rxBlckSquUpdt                  = 0           # Update status flag for receiver squelch
txBlckCFreqUpdt                = 0           # Update status flag for transmitter center frequency
txBlckSmplRUpdt                = 0           # Update status flag for transmitter sample rate
txBlckBWUpdt                   = 0           # Update status flag for transmitter analog filter BW
txBlckDFiltUpdt                = 0           # Update status flag for transmitter digital filter BW
txBlckGainUpdt                 = 0           # Update status flag for transmitter gain
pttSampCnt                     = 0           # PTT push button pushed and released sampling counter
rxTxCnt                        = 0           # Counter to simulate radio receiver-transmitter
dummyRxCentFreq                = 0.1         # Dummy receiver block center frequency during radio transmission
rxBlckVolume                   = 15          # Receiver block default volume
rxBlckCentFreq                 = 446.094e6   # Receiver block default center frequency
rxBlckSmplRate                 = 2e6         # Receiver block default sampling rate
rxBlckBndWidth                 = 5e6         # Receiver block default bandwidth
rxBlckDigFilt                  = 100e3       # Receiver block default digital filter
rxBlckGain                     = 10          # Receiver block default gain
rxBlckSquelch                  = -10         # Receiver block default squelch
dummyTxCentFreq                = 0.1         # Dummy receiver block center frequency during radio receiving
dummyTxBpskCentFreq            = 27e6        # Dummy transmitter carrier frequency during idle mode of BPSK modulation 
dummyTxBpskSmplRate            = 240e3       # Dummy sample rate during idle mode of BPSK modulation
sendBpskMsgProc                = 0           #
txBlckCentFreq                 = 446.094e6   # Transmitter block default center frequency
txBlckSmplRate                 = 2e6         # Transmitter block default sampling rate
txBlckBndWidth                 = 5e6         # Transmitter block default bandwidth
txBlckDigFilt                  = 100e3       # Transmitter block default digital filter
txBlckGain                     = 60          # Transmitter block default gain
localIpAddr                    = ''          # Local machine IP address
rxPortNo                       = 0           # Receive command port no - node-red client send the command protocol
txPortNo                       = 0           # Transmit command port no - radio daemon send the ACK/STATUS command protocol
digModuReady                   = 0           # Digital modulation transmission ready flag

digModRxFreq                   = ''          # RX block digital modulation carrier frequency
digModRxSRate                  = ''          # RX block digital modulation sample rate
digModRxGain                   = ''          # RX block digital modulation gain
digModRxSSrcSRate              = ''          # RX block digital modulation signal source sample rate
digModRxSSrcFOff               = ''          # RX block digital modulation signal source frequency offset
digModRxTcpIp                  = ''          # RX block digital modulation signal TCP server IP address
digModRxTcpPNo                 = ''          # RX block digital modulation signal TCP server port no.
digModRxBw                     = ''          # RX block digital modulation signal bandwidth
digModRxAnt                    = ''          # RX block digital modulation signal antenna selection
digModRxCalib                  = ''          # RX block digital modulation signal calibration

digModTxFreq                   = ''          # TX block digital modulation carrier frequency
digModTxSRate                  = ''          # TX block digital modulation sample rate
digModTxGain                   = ''          # TX block digital modulation gain
digModTxSSrcSRate              = ''          # TX block digital modulation signal source sample rate
digModTxSSrcFOff               = ''          # TX block digital modulation signal source frequency offset
digModTxTcpIp                  = ''          # TX block digital modulation signal TCP server IP address
digModTxTcpPNo                 = ''          # TX block digital modulation signal TCP server port no.
digModTxBw                     = ''          # TX block digital modulation signal bandwidth
digModTxAnt                    = ''          # TX block digital modulation signal antenna selection
digModTxCalib                  = ''          # TX block digital modulation signal calibration

clientConn = 0

# Additional variables for BPSK modulation - TX
txModType                     = False        # Modulation type either FM (voice) or digital modulation (text)
# Additional variables for BPSK modulation - RX
rxModType                     = False        # Modulation type either FM (voice) or digital modulation (text)
resetPTT                      = False

radioModType                  = 0            # Radio modulation type, default are analog FM modulation 
restartFlowGraph              = 4            # Default start for TOP-BLOCK flow graph in analog FM transceiver mode

# Check for macro arguments
if (len(sys.argv) > 1):
    for x in sys.argv:
        # Optional macro if we want to enable text file log
        if(x == "LOGGER"):
            backLogger = True
        # Optional macro if we want to enable raspberry pi IO interfacing
        elif x == "RASPI":
            raspiIO = True
        # Optional for radio transmit check
        elif x == "RXTXCHK":
            radioRxTxSysChk = True    

# Get the current setting
localIpAddr = localip
rxPortNo = int(rxportno)
txPortNo = int(txPortNo)

# Get the current receiver setting
rxBlckVolume = int(rxvolume)
rxBlckCentFreq = int(rxfreq)
rxBlckSmplRate = int(rxsmplrate)
rxBlckBndWidth = int(rxanabw)
rxBlckDigFilt = int(rxdigbw)
rxBlckGain = int(rxgain)
rxBlckSquelch = int(rxsquelch)

# Get the current transmitter setting
txBlckCentFreq = int(txfreq)
txBlckSmplRate = int(txsmplrate)
txBlckBndWidth = int(txanabw)
txBlckDigFilt = int(txdigbw)
txBlckGain = int(txgain)

# Get the current digital modulation receiver setting
digModRxFreq = int(digmodrxfreq)
digModRxSRate = int(digmodrxsrate)
digModRxGain = int(digmodrxgain)
digModRxSSrcSRate = int(digmodrxssrcsrate)
digModRxSSrcFOff = int(digmodrxssrcfoff)
digModRxTcpIp = digmodrxtcpip
digModRxTcpPNo = digmodrxtcppno
digModRxBw = int(digmodrxbw)
digModRxAnt = int(digmodrxant)
digModRxCalib = int(digmodrxcalib)

# Get the current digital modulation transmitter setting
digModTxFreq = int(digmodtxfreq)
digModTxSRate = int(digmodtxsrate)
digModTxGain = int(digmodtxgain)
digModTxSSrcSRate = int(digmodtxssrcsrate)
digModTxSSrcFOff = int(digmodtxssrcfoff)
digModTxTcpIp = digmodtxtcpip
digModTxTcpPNo = digmodtxtcppno
digModTxBw = int(digmodrxbw)
digModTxAnt = int(digmodrxant)
digModTxCalib = int(digmodtxcalib)

# Setup log file 
if backLogger == True:
    path = os.path.dirname(os.path.abspath(__file__))
    logger = logging.getLogger()
    logger.setLevel(logging.INFO)
    logfile = logging.handlers.TimedRotatingFileHandler('/tmp/transceiver.log', when="midnight", backupCount=3)
    formatter = logging.Formatter('%(asctime)s %(levelname)-8s %(message)s')
    logfile.setFormatter(formatter)
    logger.addHandler(logfile)

# Setup for pi GPIO interfacing
if raspiIO == True:
    import RPi.GPIO as GPIO

    # Setup for raspberry pi GPIO
    # Setup GPIO 
    GPIO.setmode(GPIO.BCM)

    # GPIO04 INPUT for radio PTT functionality
    # Active LOW
    GPIO.setup(4, GPIO.IN, pull_up_down=GPIO.PUD_UP)
    
    # GPIO02 for radio transmit indicator, RED led
    GPIO.setup(2, GPIO.OUT)

    # GPIO03 for radio receive indicator, GREEN led
    GPIO.setup(3, GPIO.OUT)

    # GPIO17 for antenna switcher control
    GPIO.setup(17, GPIO.OUT)
    
    # Turn OFF the LED for initialization
    GPIO.output(2, GPIO.HIGH)
    GPIO.output(3, GPIO.HIGH)

    # Turn OFF relay, by default the antenna in radio receiving mode 
    GPIO.output(17, GPIO.LOW)

# Doing string manipulations
def mid(s, offset, amount):
    return s[offset-1:offset+amount-1]

# BPSK demodulation packet detection - Detects complex value during RX digital modulation
class myBPSKrxdetector(gr.sync_block):  # other base classes are basic_block, decim_block, interp_block
    # GMSK demodulation progress detection embedded python block main entry script
    def __init__(self):
        gr.sync_block.__init__(
            self,
            name='myBPSKrxdetector',   # will show up in GRC
            in_sig=[np.float32],
	    out_sig=None
        )
        self.cmplexVal = 0.0
    
    # Get current GMSK demodulation RX progress value
    def getCurrRxVal (self):
        # Return current GMSK demodulation RX progress value
        return self.cmplexVal

    # Processing function
    def work(self, input_items, output_items):
        self.cmplexVal = input_items[0][0]
                	        
        return len(input_items[0])
    
# BPSK modulation packet detection - Detects complex value during TX digital modulation
class myBPSKtxdetector(gr.sync_block):
    # GMSK modulation TX progress detection embedded python block main entry script
    def __init__(self):
        gr.sync_block.__init__(
            self,
            name='myBPSKtxdetector',   # will show up in GRC
            in_sig=[np.complex64],
	    out_sig=None
        )
        self.cmplexVal = 0.0
        self.procCheck = False
        self.procEnd = False
        #self.gmskTxDetect

    # Get current BPSK modulation TX progress value
    def getCurrTxVal (self):
        # Return current GMSK modulation TX progress value
        return self.cmplexVal

    # Get current BPSK modulation text process status
    def getCurrTxtProc (self):
        # Return current BPSK modulation text process status
        return self.procEnd
    
    # Processing function
    def work(self, input_items, output_items):
        self.cmplexVal = input_items[0][0]
        self.cmplexVal = self.cmplexVal.real

        # Start check the text process
        if self.procCheck == False:
            # Text process in progress
            if self.cmplexVal > 0.0 or self.cmplexVal > -0.0:
                self.procCheck = True

        # Check the text process END
        else:
            # Text process end
            if self.cmplexVal == 0.0 or self.cmplexVal == -0.0:
                self.procCheck = False
                self.procEnd = True
                
        return len(input_items[0])

# Audio detection embedded python block class - Sink block, no output pin
class myaudiodetector(gr.sync_block):  # other base classes are basic_block, decim_block, interp_block
    # Audio detection embedded python block main entry script            
    def __init__(self, item=np.uint32, vlen=1):  # only default arguments here
        gr.sync_block.__init__(
            self,
            name='myaudiodetector',   # will show up in GRC
            in_sig=[(item, vlen)],
            out_sig=None
        )
        self.audioDetect = False
    # Get current audio detection status 
    def getAudioStatus(self):
        # Return the current status of audio status
        return self.audioDetect

    # Processing function
    def work(self, input_items, output_items):
        # Receive audio signal from FM receiver block        
        if abs(input_items[0][0]) > 0.0:
            self.audioDetect = True
            
        # By default no audio received from FM receiver block 
        else:
            self.audioDetect = False
                    
        return len(input_items[0])

# Class for BPSK messaging
class bpsk_messaging(gr.top_block):

    def __init__(self, hdr_format=digital.header_format_default(digital.packet_utils.default_access_code, 0)
    , my_const=digital.constellation_calcdist((digital.psk_2()[0]), (digital.psk_2()[1]), 2, 1).base()
    ):
        global digModRxFreq
        global digModRxSRate
        global digModRxGain
        global digModRxTcpIp
        global digModRxTcpPNo
        global digModRxSSrcSRate
        global digModRxSSrcFOff
        global digModRxBw
        global digModRxAnt
        global digModRxCalib
        
        global digModTxFreq
        global digModTxSRate
        global digModTxGain
        global digModTxTcpIp
        global digModTxTcpPNo
        global digModTxSSrcSRate
        global digModTxSSrcFOff
        global digModTxBw
        global digModTxAnt
        global digModRxCalib
        
        gr.top_block.__init__(self, "BPSK Messaging")

        ##################################################
        # Parameters
        ##################################################
        self.hdr_format = hdr_format
        self.my_const = my_const

        ##################################################
        # Variables
        ##################################################
        self.sps_TX = sps_TX = 40
        self.nfilts = nfilts = 32
        self.EBW = EBW = .35
        self.sps_RX = sps_RX = 40/10
        #self.samp_rate = samp_rate = 240E3

        # Configurable variable
        # Receiver/source block parameters
        self.rxfreq = rxfreq = digModRxFreq
        self.samp_rate_rx = samp_rate_rx = digModRxSRate
        self.bwidth_rx = bwidth_rx = digModRxBw
        self.gain_rx = gain_rx = digModRxGain
        self.ant_rx = ant_rx = digModRxAnt
        self.calib_rx = calib_rx = digModRxCalib
        self.ipaddr_rx = ipaddr_rx = digModRxTcpIp
        self.portno_rx = portno_rx = digModRxTcpPNo
        self.sigsrcsmplerate_rx = sigsrcsmplerate_rx = digModRxSSrcSRate
        self.sisrcoffset_rx = sisrcoffset_rx = digModRxSSrcFOff

        # Transmitter/sink block parameters
        self.txfreq = txfreq = digModTxFreq
        self.samp_rate_tx = samp_rate_tx = digModTxSRate
        self.bwidth_tx = bwidth_tx = digModTxBw
        self.gain_tx = gain_tx = digModTxGain
        self.ant_tx = ant_tx = digModTxAnt
        self.calib_tx = calib_tx = digModTxCalib
        self.ipaddr_tx = ipaddr_tx = digModTxTcpIp
        self.portno_tx = portno_tx = digModTxTcpPNo
        self.sigsrcsmplerate_tx = sigsrcsmplerate_tx = digModTxSSrcSRate
        self.sisrcoffset_tx = sisrcoffset_tx = digModTxSSrcFOff
        
        self.low_pass_filt_trans_width = low_pass_filt_trans_width = 1e6
        self.low_pass_filt_sampl_rate = low_pass_filt_sampl_rate = 2.048e6
        self.low_pass_filt_deci = low_pass_filt_deci = 1
        self.low_pass_filt_cut_off = low_pass_filt_cut_off = 100e3
        self.freq_offset_value = freq_offset_value = 30E3
        self.center_freq = center_freq = 430E6
        
        self.RRC_filter_taps = RRC_filter_taps = firdes.root_raised_cosine(nfilts, nfilts, 1.0, EBW, 5*sps_TX*nfilts)
          
        ##################################################
        # Blocks
        ##################################################
        self.rational_resampler_xxx_0 = filter.rational_resampler_ccc(
                interpolation=1,
                decimation=int(sps_TX/sps_RX),
                taps=None,
                fractional_bw=None,
        )
        self.pfb_arb_resampler_xxx_0 = pfb.arb_resampler_ccf(
        	  sps_TX,
                  taps=(RRC_filter_taps),
        	  flt_size=nfilts)
        self.pfb_arb_resampler_xxx_0.declare_sample_delay(0)

        ##################################################
        # Additional blocks for BPSK mosulation
        ##################################################
        # Block to detect complex value during text messaging process
        self.epy_block_0 = myBPSKtxdetector()
        
        self.limesdr_source_0 = limesdr.source('', 0, '')
        self.limesdr_source_0.set_sample_rate(samp_rate_rx)
        self.limesdr_source_0.set_center_freq(rxfreq, 0)
        self.limesdr_source_0.set_bandwidth(bwidth_rx,0)
        self.limesdr_source_0.set_gain(gain_rx,0)
        self.limesdr_source_0.set_antenna(ant_rx,0)
        self.limesdr_source_0.calibrate(calib_rx, 0)
            
        self.limesdr_sink_0_0 = limesdr.sink('', 0, '', '')
        self.limesdr_sink_0_0.set_sample_rate(samp_rate_tx)
        self.limesdr_sink_0_0.set_center_freq(txfreq, 0)
        self.limesdr_sink_0_0.set_bandwidth(bwidth_tx,0)
        self.limesdr_sink_0_0.set_gain(gain_tx,0)
        self.limesdr_sink_0_0.set_antenna(ant_tx,0)
        self.limesdr_sink_0_0.calibrate(calib_tx, 0)
            
        self.digital_protocol_formatter_bb_0 = digital.protocol_formatter_bb(hdr_format, 'len_key')
        self.digital_pfb_clock_sync_xxx_0 = digital.pfb_clock_sync_ccf(sps_RX, 6.28/400.0*2, (RRC_filter_taps), nfilts, nfilts/2, 1.5, 1)
        self.digital_fll_band_edge_cc_0 = digital.fll_band_edge_cc(sps_RX, EBW, 45, .02)
        self.digital_diff_encoder_bb_0 = digital.diff_encoder_bb(2)
        self.digital_diff_decoder_bb_0 = digital.diff_decoder_bb(2)
        self.digital_crc32_async_bb_1 = digital.crc32_async_bb(False)
        self.digital_crc32_async_bb_0 = digital.crc32_async_bb(True)
        self.digital_costas_loop_cc_0 = digital.costas_loop_cc(.01, 2, False)
        self.digital_correlate_access_code_xx_ts_1_0 = digital.correlate_access_code_bb_ts(digital.packet_utils.default_access_code,
          2, 'len_key2')
        self.digital_constellation_soft_decoder_cf_0 = digital.constellation_soft_decoder_cf(my_const)
        self.digital_cma_equalizer_cc_0 = digital.cma_equalizer_cc(11, 1, .01, 1)
        self.digital_chunks_to_symbols_xx_0_0 = digital.chunks_to_symbols_bc((my_const.points()), 1)
        self.digital_burst_shaper_xx_0 = digital.burst_shaper_cc((numpy.ones(500)), 4000, 4000, True, 'len_key')
        (self.digital_burst_shaper_xx_0).set_block_alias("burst_shaper0")
        self.digital_binary_slicer_fb_0 = digital.binary_slicer_fb()
        self.blocks_tagged_stream_to_pdu_0 = blocks.tagged_stream_to_pdu(blocks.byte_t, 'len_key2')
        self.blocks_tagged_stream_mux_0 = blocks.tagged_stream_mux(gr.sizeof_char*1, 'len_key', 0)
        self.blocks_tagged_stream_multiply_length_0 = blocks.tagged_stream_multiply_length(gr.sizeof_gr_complex*1, 'len_key', sps_TX)
        self.blocks_socket_pdu_1 = blocks.socket_pdu("TCP_SERVER", ipaddr_rx, portno_rx, 10000, False)
        self.blocks_socket_pdu_0 = blocks.socket_pdu("TCP_SERVER", ipaddr_rx, portno_tx, 10000, False)
        self.blocks_repack_bits_bb_0_0_0 = blocks.repack_bits_bb(1, 8, 'len_key2', False, gr.GR_MSB_FIRST)
        self.blocks_repack_bits_bb_0_0 = blocks.repack_bits_bb(8, my_const.bits_per_symbol(), 'len_key', False, gr.GR_MSB_FIRST)
        self.blocks_pdu_to_tagged_stream_1 = blocks.pdu_to_tagged_stream(blocks.byte_t, 'len_key')
        self.blocks_multiply_xx_1 = blocks.multiply_vcc(1)
        self.blocks_multiply_xx_0 = blocks.multiply_vcc(1)
        self.blocks_multiply_const_vxx_0 = blocks.multiply_const_vcc((0.5, ))
        self.blocks_message_debug_0 = blocks.message_debug()
        self.analog_sig_source_x_1 = analog.sig_source_c(sigsrcsmplerate_rx, analog.GR_COS_WAVE, -freq_offset_value, 1, 0)
        self.analog_sig_source_x_0 = analog.sig_source_c(sigsrcsmplerate_tx, analog.GR_COS_WAVE, freq_offset_value, 1, 0)
        self.analog_pwr_squelch_xx_0 = analog.pwr_squelch_cc(-20, .01, 0, True)
        self.analog_feedforward_agc_cc_0 = analog.feedforward_agc_cc(1024/2, 1.0)

        ##################################################
        # Connections
        ##################################################
        self.msg_connect((self.blocks_socket_pdu_0, 'pdus'), (self.digital_crc32_async_bb_1, 'in'))    
        self.msg_connect((self.blocks_tagged_stream_to_pdu_0, 'pdus'), (self.digital_crc32_async_bb_0, 'in'))    
        self.msg_connect((self.digital_crc32_async_bb_0, 'out'), (self.blocks_message_debug_0, 'print'))    
        self.msg_connect((self.digital_crc32_async_bb_0, 'out'), (self.blocks_socket_pdu_1, 'pdus'))    
        self.msg_connect((self.digital_crc32_async_bb_1, 'out'), (self.blocks_pdu_to_tagged_stream_1, 'pdus'))    
        self.connect((self.analog_feedforward_agc_cc_0, 0), (self.digital_pfb_clock_sync_xxx_0, 0))    
        self.connect((self.analog_pwr_squelch_xx_0, 0), (self.digital_fll_band_edge_cc_0, 0))    
        self.connect((self.analog_sig_source_x_0, 0), (self.blocks_multiply_xx_0, 1))    
        self.connect((self.analog_sig_source_x_1, 0), (self.blocks_multiply_xx_1, 1))    
        self.connect((self.blocks_multiply_const_vxx_0, 0), (self.blocks_multiply_xx_0, 0))    
        self.connect((self.blocks_multiply_xx_0, 0), (self.limesdr_sink_0_0, 0))
        
        # Additional connections
        self.connect((self.blocks_multiply_xx_0, 0), (self.epy_block_0, 0))
        
        self.connect((self.blocks_multiply_xx_1, 0), (self.rational_resampler_xxx_0, 0))    
        self.connect((self.blocks_pdu_to_tagged_stream_1, 0), (self.blocks_tagged_stream_mux_0, 1))    
        self.connect((self.blocks_pdu_to_tagged_stream_1, 0), (self.digital_protocol_formatter_bb_0, 0))    
        self.connect((self.blocks_repack_bits_bb_0_0, 0), (self.digital_diff_encoder_bb_0, 0))    
        self.connect((self.blocks_repack_bits_bb_0_0_0, 0), (self.blocks_tagged_stream_to_pdu_0, 0))    
        self.connect((self.blocks_tagged_stream_multiply_length_0, 0), (self.blocks_multiply_const_vxx_0, 0))    
        self.connect((self.blocks_tagged_stream_mux_0, 0), (self.blocks_repack_bits_bb_0_0, 0))    
        self.connect((self.digital_binary_slicer_fb_0, 0), (self.digital_diff_decoder_bb_0, 0))    
        self.connect((self.digital_burst_shaper_xx_0, 0), (self.pfb_arb_resampler_xxx_0, 0))    
        self.connect((self.digital_chunks_to_symbols_xx_0_0, 0), (self.digital_burst_shaper_xx_0, 0))    
        self.connect((self.digital_cma_equalizer_cc_0, 0), (self.digital_constellation_soft_decoder_cf_0, 0))    
        self.connect((self.digital_constellation_soft_decoder_cf_0, 0), (self.digital_binary_slicer_fb_0, 0))    
        self.connect((self.digital_correlate_access_code_xx_ts_1_0, 0), (self.blocks_repack_bits_bb_0_0_0, 0))    
        self.connect((self.digital_costas_loop_cc_0, 0), (self.digital_cma_equalizer_cc_0, 0))    
        self.connect((self.digital_diff_decoder_bb_0, 0), (self.digital_correlate_access_code_xx_ts_1_0, 0))    
        self.connect((self.digital_diff_encoder_bb_0, 0), (self.digital_chunks_to_symbols_xx_0_0, 0))    
        self.connect((self.digital_fll_band_edge_cc_0, 0), (self.analog_feedforward_agc_cc_0, 0))    
        self.connect((self.digital_pfb_clock_sync_xxx_0, 0), (self.digital_costas_loop_cc_0, 0))    
        self.connect((self.digital_protocol_formatter_bb_0, 0), (self.blocks_tagged_stream_mux_0, 0))    
        self.connect((self.limesdr_source_0, 0), (self.blocks_multiply_xx_1, 0))    
        self.connect((self.pfb_arb_resampler_xxx_0, 0), (self.blocks_tagged_stream_multiply_length_0, 0))    
        self.connect((self.rational_resampler_xxx_0, 0), (self.analog_pwr_squelch_xx_0, 0))    

    # Get text messaging status during START and END of transmisson
    def get_bpsktxstatus(self):
        return self.epy_block_0.getCurrTxtProc()

    # Get radio transmission complex value during transmit process
    def get_txCurrVal(self):
        return self.epy_block_0.getCurrTxVal()
    
    def get_hdr_format(self):
        return self.hdr_format

    # Set NEW value for Protocol Formatter (Format Obj.) block
    def set_hdr_format(self, hdr_format):
        self.hdr_format = hdr_format

    def get_my_const(self):
        return self.my_const

    # Set NEW constant parameter for Repack Bits (Bits per output byte) and Chucnks to Symbols (Symbol Table) block
    def set_my_const(self, my_const):
        self.my_const = my_const

    def get_sps_TX(self):
        return self.sps_TX

    # Set NEW value for for RRC Filter Taps (Num Taps), Tagged Stream Multiply Length Tag (Length Scalar) and Polyphase Arbitrary Resampler
    # (Resampling Rate) block
    def set_sps_TX(self, sps_TX):
        self.sps_TX = sps_TX
        self.pfb_arb_resampler_xxx_0.set_rate(self.sps_TX)
        self.blocks_tagged_stream_multiply_length_0.set_scalar(self.sps_TX)

    def get_nfilts(self):
        return self.nfilts

    # Set NEW value for Polyphase Arbitrary Resampler (Number Of Filters) and RRC Filter Taps (Num Taps) block
    def set_nfilts(self, nfilts):
        self.nfilts = nfilts

    def get_EBW(self):
        return self.EBW

    # Set NEW value for RRC Filter Taps (Excess BW) 
    def set_EBW(self, EBW):
        self.EBW = EBW

    def get_sps_RX(self):
        return self.sps_RX

    # Set NEW value for FLL Band-Edge (Samples Per Symbol), Rational Resampler (Decimation), Polyphase Clock Sync (Samples/Symbol),
    # and FLL Band-Edge (Samples/Symbol)
    def set_sps_RX(self, sps_RX):
        self.sps_RX = sps_RX

    def get_samp_rate_rx_src(self):
        return self.samp_rate_rx

    # Set NEW value for receiver/source block sample rate for limesdr
    def set_samp_rate_rx_src(self, samp_rate_rx_src):
        self.samp_rate_rx = samp_rate_rx_src
        self.limesdr_source_0.set_sample_rate(self.samp_rate_rx)

    def get_samp_rate_tx_src(self):
        return self.samp_rate_tx

    # Set NEW value for transmitter/source block sample rate for limesdr
    def set_samp_rate_tx_src(self, samp_rate_tx_src):
        self.samp_rate_tx = samp_rate_tx_src
        self.limesdr_sink_0_0.set_sample_rate(self.samp_rate_tx)

    def get_freq_rx_src(self):
        return self.rxfreq

    # Set NEW for receiver/source block frequency for limesdr
    def set_freq_rx_src(self, freq_rx_src):
        self.rxfreq = freq_rx_src
        self.limesdr_source_0.set_center_freq(self.rxfreq, 0)

    def get_freq_tx_src(self):
        return self.txfreq

    # Set NEW for transmitter/sink block frequency for limesdr
    def set_freq_tx_src(self, freq_tx_src):
        self.txfreq = freq_tx_src
        self.limesdr_sink_0_0.set_center_freq(self.txfreq, 0)

    def get_ana_bwidth_rx_src(self):
        return self.bwidth_rx

    # Set NEW for receiver/source block analog bandwidth for limesdr
    def set_ana_bwidth_rx_src(self, ana_bwidth_rx_src): 
        self.bwidth_rx = ana_bwidth_rx_src
        self.limesdr_source_0.set_bandwidth(self.bwidth_rx,0)

    def get_ana_bwidth_rx_src(self):
        return self.bwidth_rx

    # Set NEW for transmitter/source block analog bandwidth for limesdr
    def set_ana_bwidth_tx_src(self, ana_bwidth_tx_src): 
        self.bwidth_tx = ana_bwidth_tx_src
        self.limesdr_sink_0_0.set_bandwidth(self.bwidth_tx,0)

    def get_gain_rx_src(self):
        return self.gain_rx

    # Set NEW for receiver/source block gain for limesdr
    def get_gain_rx_src(self, gain_rx_src):
        self.gain_rx = gain_rx_src
        self.limesdr_source_0.set_gain(self.gain_rx,0)
        
    def get_gain_tx_src(self):
        return self.gain_tx

    # Set NEW for transmitter/sink block gain for limesdr
    def get_gain_tx_src(self, gain_tx_src):
        self.gain_tx = gain_tx_src
        self.limesdr_sink_0_0.set_gain(self.gain_tx,0)

    def get_ant_rx_src(self):
        return self.ant_rx

    # Set NEW for receiver/source block antenna for limesdr
    def set_ant_rx_src(self, ant_rx_src):
        self.ant_rx = ant_rx_src
        self.limesdr_source_0.set_antenna(self.ant_rx,0)
    
    def get_ant_tx_src(self):
        return self.ant_tx

    # Set NEW for transmitter/sink block antenna for limesdr
    def set_ant_tx_src(self, ant_tx_src):
        self.ant_tx = ant_tx_src
        self.limesdr_sink_0_0.set_antenna(self.ant_tx,0)

    def get_calib_rx_src(self):
        return self.calib_rx

    # Set NEW for receiver/source block calibration for limesdr
    def set_calib_rx_src(self, calib_rx_src):
        self.calib_rx = calib_rx_src
        self.limesdr_source_0.calibrate(self.calib_rx, 0)

    def get_calib_tx_src(self):
        return self.calib_tx

    # Set NEW for transmitter/sink block calibration for limesdr
    def set_calib_tx_src(self, calib_tx_src):
        self.calib_tx = calib_tx_src
        self.limesdr_sink_0_0.calibrate(calib_tx, 0)

    def get_sigsrcsmplrate_rx(self):
        return self.sigsrcsmplerate_rx

    # Set NEW for receiver signal source sample rate 
    def set_sigsrcsmplrate_rx(self, sigsrcsmplrate_rx):
        self.sigsrcsmplerate_rx = sigsrcsmplrate_rx
        self.analog_sig_source_x_1.set_sampling_freq(self.sigsrcsmplerate_rx)

    def get_sigsrcsmplrate_tx(self):
        return self.sigsrcsmplerate_tx

    # Set NEW for transmitter signal source sample rate 
    def set_sigsrcsmplrate_tx(self, sigsrcsmplrate_tx):
        self.sigsrcsmplerate_tx = sigsrcsmplrate_tx
        self.analog_sig_source_x_0.set_sampling_freq(self.sigsrcsmplerate_tx)

    def get_low_pass_filt_trans_width(self):
        return self.low_pass_filt_trans_width

    def set_low_pass_filt_trans_width(self, low_pass_filt_trans_width):
        self.low_pass_filt_trans_width = low_pass_filt_trans_width

    def get_low_pass_filt_sampl_rate(self):
        return self.low_pass_filt_sampl_rate

    def set_low_pass_filt_sampl_rate(self, low_pass_filt_sampl_rate):
        self.low_pass_filt_sampl_rate = low_pass_filt_sampl_rate

    def get_low_pass_filt_deci(self):
        return self.low_pass_filt_deci

    def set_low_pass_filt_deci(self, low_pass_filt_deci):
        self.low_pass_filt_deci = low_pass_filt_deci

    def get_low_pass_filt_cut_off(self):
        return self.low_pass_filt_cut_off

    def set_low_pass_filt_cut_off(self, low_pass_filt_cut_off):
        self.low_pass_filt_cut_off = low_pass_filt_cut_off

    def get_freq_offset_rx(self):
        return self.sisrcoffset_rx

    # Set NEW for receiver signal source offset frequency
    def set_freq_offset_rx(self, freq_offset_rx):
        self.sisrcoffset_rx = freq_offset_rx
        self.analog_sig_source_x_1.set_frequency(-self.sisrcoffset_rx)

    def get_freq_offset_tx(self):
        return self.sisrcoffset_tx

    # Set NEW for transmitter signal source offset frequency
    def set_freq_offset_tx(self, freq_offset_tx):
        self.sisrcoffset_tx = freq_offset_tx
        self.analog_sig_source_x_0.set_frequency(self.self.sisrcoffset_tx)
        
    def get_freq_offset_value(self):
        return self.freq_offset_value

    def set_freq_offset_value(self, freq_offset_value):
        self.freq_offset_value = freq_offset_value
        self.analog_sig_source_x_1.set_frequency(-self.freq_offset_value)
        self.analog_sig_source_x_0.set_frequency(self.freq_offset_value)

    def get_RRC_filter_taps(self):
        return self.RRC_filter_taps

    def set_RRC_filter_taps(self, RRC_filter_taps):
        self.RRC_filter_taps = RRC_filter_taps
        self.pfb_arb_resampler_xxx_0.set_taps((self.RRC_filter_taps))
        self.digital_pfb_clock_sync_xxx_0.update_taps((self.RRC_filter_taps))

# GNU radio class for FM receiver
class receive_path(gr.hier_block2):
    
    # Class initialization
    def __init__(self):
        global rxBlckVolume
        global rxBlckCentFreq
        global rxBlckSmplRate
        global rxBlckBndWidth
        global rxBlckDigFilt
        global rxBlckGain
        global rxBlckSquelch
        global rxModType
                
        gr.hier_block2.__init__(self, "receive_path",
                                gr.io_signature(0, 0, 0), # Null signature
                                gr.io_signature(0, 0, 0))

        ##################################################
        # Variables - That necessary for future configuration
        # Receiver important parameters
        ##################################################
        self.varVol = varVol = rxBlckVolume          # Value: 15
        self.rxfreq = rxfreq = rxBlckCentFreq        # Value: 446.094e6
        self.smplrate = smplrate = rxBlckSmplRate    # Value: 2e6
        self.bwidth = bwidth = rxBlckBndWidth        # Value: 5e6
        self.digfilt = digfilt = rxBlckDigFilt       # Value: 100e3
        self.gain = gain = rxBlckGain                # Value: 10
        self.varSquelch = varSquelch = rxBlckSquelch # Value: -10

        ##################################################
        # Blocks for FM demodulation - Voice communication
        ##################################################
        # Block Rational Resampler
        self.rational_resampler_xxx_1 = filter.rational_resampler_ccc(
                interpolation=48,
                decimation=200,
                taps=None,
                fractional_bw=None,
        )
        # Block Low Pass Filter
        self.low_pass_filter_0 = filter.fir_filter_ccf(1, firdes.low_pass(
        	1, 2e6, 100e3, 1e6, firdes.WIN_HAMMING, 6.76))
        # Block LimeSDR for radio receiver
        self.limesdr_source_0 = limesdr.source('', 0, '')
        self.limesdr_source_0.set_sample_rate(smplrate)
        self.limesdr_source_0.set_center_freq(rxfreq, 0)
        self.limesdr_source_0.set_bandwidth(bwidth,0)
        self.limesdr_source_0.set_digital_filter(digfilt,0)
        self.limesdr_source_0.set_gain(gain)
        self.limesdr_source_0.set_antenna(255,0)
        #self.limesdr_source_0.calibrate(5e6, 0)
                
        # Block Simple Squelch
        self.analog_simple_squelch_cc_0 = analog.simple_squelch_cc(varSquelch, 1)
        # Block Audio Sink
        self.audio_sink_0 = audio.sink(48000, '', True)
        # Block wide FM demodulation
        self.analog_wfm_rcv_0 = analog.wfm_rcv(
        	quad_rate=480e3,
        	audio_decimation=10,
        )
        # Block Multiply Const 
        self.blocks_multiply_const_vxx_0 = blocks.multiply_const_vff((varVol, ))
        # Embedded python block class for audio detection 
        self.epy_block_0 = myaudiodetector(item=np.float32)

        ##################################################
        # Connections for FM demodulation - Voice Communication
        ##################################################        
        self.connect((self.limesdr_source_0, 0, 0), (self.low_pass_filter_0, 0))
        self.connect((self.low_pass_filter_0, 0), (self.rational_resampler_xxx_1, 0))
        self.connect((self.rational_resampler_xxx_1, 0), (self.analog_simple_squelch_cc_0, 0))
        self.connect((self.analog_simple_squelch_cc_0, 0), (self.analog_wfm_rcv_0, 0))
        self.connect((self.analog_wfm_rcv_0, 0), (self.blocks_multiply_const_vxx_0, 0))
        self.connect((self.blocks_multiply_const_vxx_0, 0), (self.audio_sink_0, 0))
        self.connect((self.blocks_multiply_const_vxx_0, 0), (self.epy_block_0, 0))
          
    # Get receiver audio detection status
    def get_rxstatus(self):
        return self.epy_block_0.getAudioStatus()

    # Set new value for receiver volume control
    def set_varVol(self, varVol):
        self.varVol = varVol
        self.blocks_multiply_const_vxx_0.set_k((self.varVol, ))

    # Set new value for receiver squelch threshold
    def set_varSquelch(self, varSquelch):
        self.varSquelch = varSquelch
        self.analog_simple_squelch_cc_0.set_threshold(self.varSquelch)
        
    # Set new value for receiver frequency
    def set_rxfrequency(self, rxfreq):
        self.rxfreq = rxfreq
        self.limesdr_source_0.set_center_freq(self.rxfreq, 0)

    # Set sample rate for receiver block
    def set_rxsample_rate (self, smplrate):
        self.smplrate = smplrate
        self.limesdr_source_0.set_sample_rate(self.smplrate)
        
    # Set bandwidth for receiver block
    def set_bwidth (self, bwidth):
        self.bwidth = bwidth
        self.limesdr_source_0.set_bandwidth(bwidth,0)

    # Set digital filter for receiver block
    def set_dig_filter (self, digfilt):
        self.digfilt = digfilt
        self.limesdr_source_0.set_digital_filter(self.digfilt,0)

    # Set gain for receiver block
    def set_gain (self, gain):
        self.gain = gain
        self.limesdr_source_0.set_gain(self.gain,0)

    def reset_flowGraph (self):
        self.__init__()

# GNU radio class for transmitter
class transmit_path(gr.hier_block2):

    # Class initialization
    def __init__(self):
        global dummyTxCentFreq
        #global txBlckCentFreq
        global txBlckSmplRate
        global txBlckBndWidth
        global txBlckDigFilt
        global txBlckGain
        global txModType
                
        gr.hier_block2.__init__(self, "transmit_path",
                                gr.io_signature(0, 0, 0), # Null signature
                                gr.io_signature(0, 0, 0))

        ##################################################
        # Variables - That necessary for future configuration
        # Transmitter important parameters
        ##################################################
        self.txfreq = txfreq = dummyTxCentFreq    # Value: 0.1
        #self.txfreq = txfreq = txBlckCentFreq    # Value: 0.1
        self.smplrate = smplrate = txBlckSmplRate # Value: 2e6
        self.bwidth = bwidth = txBlckBndWidth     # Value: 5e6
        self.digfilt = digfilt = txBlckDigFilt    # Value: 100e3
        self.gain = gain = txBlckGain             # Value: 60

        ##################################################
        # Blocks for FM modulation - Voice communication
        ##################################################
        # Block Rational Resampler
        self.rational_resampler_xxx_0 = filter.rational_resampler_ccf(
                interpolation=25,
                decimation=6,
                taps=None,
                fractional_bw=None,
        )
        # Block LimeSDR Transceiver
        self.limesdr_sink_0 = limesdr.sink('', 0, '', '')
        self.limesdr_sink_0.set_sample_rate(smplrate)
        self.limesdr_sink_0.set_center_freq(txfreq, 0)
        self.limesdr_sink_0.set_bandwidth(bwidth,0)
        self.limesdr_sink_0.set_digital_filter(digfilt,0)
        self.limesdr_sink_0.set_gain(gain,0)
        self.limesdr_sink_0.set_antenna(255,0)
        #self.limesdr_sink_0.calibrate(5e6, 0)
        
        # Block audio source for voice communication
        self.audio_source_0 = audio.source(48000, '', True)
        # Block Narrow Band FM modulator
        self.analog_nbfm_tx_0_0 = analog.nbfm_tx(
        	audio_rate=48000,
        	quad_rate=480000,
        	tau=75e-6,
        	max_dev=2e3,
        	fh=-1.0,
                )
        
        ##################################################
        # Connections for FM modulation - Voice Communication
        ##################################################
        self.connect((self.audio_source_0, 0), (self.analog_nbfm_tx_0_0, 0))
        self.connect((self.analog_nbfm_tx_0_0, 0), (self.rational_resampler_xxx_0, 0))
        self.connect((self.rational_resampler_xxx_0, 0), (self.limesdr_sink_0, 0))
        
    # Get radio transmission complex value during transmit process
    def get_txCurrVal(self):
        return self.epy_block_0.getCurrTxVal()

    # Set NEW value for transmit frequency
    def set_txfrequency(self, txfreq):
        self.txfreq = txfreq
        self.limesdr_sink_0.set_center_freq(self.txfreq, 0)

    # Set NEW sample rate for transmitter block
    def set_txsample_rate (self, smplrate):
        self.smplrate = smplrate
        self.limesdr_sink_0.set_sample_rate(self.smplrate)
        
    # Set NEW analog filter bandwidth for transmitter block
    def set_bwidth (self, bwidth):
        self.bwidth = bwidth
        self.limesdr_sink_0.set_bandwidth(bwidth,0)

    # Set NEW digital filter bandwidth for transmitter block
    def set_dig_filter (self, digfilt):
        self.digfilt = digfilt
        self.limesdr_sink_0.set_digital_filter(self.digfilt,0)

    # Set NEW gain for transmitter block
    def set_gain (self, gain):
        self.gain = gain
        self.limesdr_sink_0.set_gain(self.gain,0)
    
    def reset_flowGraph (self):
        self.__init__()
    
# GNU radio class for FM transceiver - Multiple flow graphs using gr.heir
class FM_Transceiver(gr.top_block):
    
    def __init__(self):
        gr.top_block.__init__(self, "FM_Transceiver")

        self.tx_path = transmit_path()
        self.rx_path = receive_path()

        self.connect(self.tx_path)
        self.connect(self.rx_path)

    ##################################################
    # Radio Transmit Process Get Function
    ##################################################
    def proc_reset_transmit(self):
        self.tx_path.reset_flowGraph()
    # When transmitting, set the transmit frequency based on the current setting
    # For receiver during transmission, set the receive frequency for default in active frequency - 0.1
    def proc_transmit(self, volume, txfreq):
        self.tx_path.set_txfrequency(txfreq)
        self.rx_path.set_varVol(volume)
        
    #def proc_transmit(self, txfreq, rxfreq):
    #    self.tx_path.set_txfrequency(txfreq)
        #self.rx_path.set_rxfrequency(rxfreq)
        #self.rx_path.set_varVol(0)

    # Get radio transmission complex value during transmit process
    def get_transmit_currvalue(self):
        return self.tx_path.get_txCurrVal()
    
    # Set transmitter block center frequency
    def set_transmit_centfreq(self, centfreq):
        self.tx_path.set_txfrequency(centfreq)

    # Set transmitter block sampling rate
    def set_transmit_samplrate(self, smplrate):
        self.tx_path.set_txsample_rate(smplrate)

    # Set transmitter block bandwidth
    def set_transmit_bndwidth(self, bwidth):
        self.tx_path.set_bwidth(bwidth)

    # Set transmitter block digital filter
    def set_transmit_digfilter(self, digitfilt):
        self.tx_path.set_dig_filter(digitfilt)

    # Set transmitter block gain
    def set_transmit_gain(self, gain):
        self.tx_path.set_gain(gain)

    ##################################################
    # Radio Receive Process Get Function
    ##################################################
    def proc_reset_receive(self):
        self.rx_path.reset_flowGraph()
    # When receiving, set the receive frequency based on the current setting
    # For transmitter during receiving, set the transmit frequency for default in active frequency - 0.1
    def proc_receive (self, volume, txfreq):
        self.tx_path.set_txfrequency(txfreq)
        self.rx_path.set_varVol(volume)
    
    #def proc_receive(self, txfreq, rxfreq):
    #    self.tx_path.set_txfrequency(txfreq)
    #    self.rx_path.set_rxfrequency(rxfreq)
        #self.rx_path.set_varVol(20)

    # Get current receiving audio status 
    def get_audiostatus(self):
        return self.rx_path.get_rxstatus()

    # Set receiver block volume
    def set_receive_varVol(self, volume):
        self.rx_path.set_varVol(volume)

    # Set receiver block squelch threshold
    def set_receive_varSquelch(self, squelch):
        self.rx_path.set_varSquelch(squelch)
        
    # Set receiver block center frequency
    def set_receive_centfreq(self, centfreq):
        self.rx_path.set_rxfrequency(centfreq)

    # Set receiver block sampling rate
    def set_receive_samplrate(self, smplrate):
        self.rx_path.set_rxsample_rate(smplrate)

    # Set receiver block bandwidth
    def set_receive_bndwidth(self, bwidth):
        self.rx_path.set_bwidth(bwidth)

    # Set receiver block digital filter
    def set_receive_digfilter(self, digitfilt):
        self.rx_path.set_dig_filter(digitfilt)

    # Set receiver block gain
    def set_receive_gain(self, gain):
        self.rx_path.set_gain(gain)
   
# Radio receiver-transmitter functionalities check
def radioRxTxCheck (threadname, delay):
    global top_block
    global rxTxCnt
    global txBlckCentFreq
    global dummyRxCentFreq
    global rxBlckCentFreq
    global dummyTxCentFreq
    
    detAudSta = False
    testRxTx = False
        
    while True:
        time.sleep(delay)
        
        # Start checking current radio mode
        detAudStat = top_block.get_audiostatus()
        # FM receiver block detects the incoming audio
        if detAudStat == True:
            # Write to logger
            if backLogger == True:
                logger.info("THREAD_RX_CHK: Incoming AUDIO available")
            # Print statement
            else:
                print "THREAD_RX_CHK: Incoming AUDIO available"
                
        # FM receiver block NOT detects any incoming audio
        else:
            # Write to logger
            if backLogger == True:
                logger.info("THREAD_RX_CHK: Incoming AUDIO NOT available")
            # Print statement
            else:
                print "THREAD_RX_CHK: Incoming AUDIO NOT available"

        # Increment receiver-transmitter simulation counter
        rxTxCnt += 1

        # By default the radio are in receiver mode
        # Reach 10 seconds, simulate radio as a transmitter mode
        if testRxTx == False and rxTxCnt == 40:
            # Write to logger
            if backLogger == True:
                logger.info("THREAD_RX_CHK: Radio in TX mode")
            # Print statement
            else:
                print "THREAD_RX_CHK: Radio in TX mode"
                
            # Set the new radio operation mode - Radio in tx mode
            #top_block.set_transmit(0, 446.094e6)
            top_block.proc_transmit(txBlckCentFreq, dummyRxCentFreq)

            testRxTx = True
            rxTxCnt = 0

        # Reach sub sequent 10 seconds, simulate radio as a receiver mode
        elif testRxTx == True and rxTxCnt == 40:
            # Write to logger
            if backLogger == True:
                logger.info("THREAD_RX_CHK: Radio in RX mode")
            # Print statement
            else:
                print "THREAD_RX_CHK: Radio in RX mode"
                
            # Set the new radio operation mode - Radio in rx mode
            #top_block.set_receive(10, 0.1)
            top_block.proc_receive(dummyTxCentFreq, rxBlckCentFreq)

            testRxTx = False
            rxTxCnt = 0
    
# Update radio configuration file for transmitter and receiver block
def updateRadioConfig ():
    global localIpAddr
    global rxPortNo
    global txPortNo
    global rxBlckVolume 
    global rxBlckCentFreq 
    global rxBlckSmplRate 
    global rxBlckBndWidth 
    global rxBlckDigFilt 
    global rxBlckGain 
    global rxBlckSquelch 
    global txBlckCentFreq 
    global txBlckSmplRate 
    global txBlckBndWidth 
    global txBlckDigFilt 
    global txBlckGain

    global digModRxFreq
    global digModRxSRate                  
    global digModRxGain                  
    global digModRxSSrcSRate              
    global digModRxSSrcFOff               
    global digModRxTcpIp                  
    global digModRxTcpPNo                 
    global digModRxBw                     
    global digModRxAnt                    
    global digModRxCalib                  

    global digModTxFreq                   
    global digModTxSRate                  
    global digModTxGain                   
    global digModTxSSrcSRate              
    global digModTxSSrcFOff               
    global digModTxTcpIp                  
    global digModTxTcpPNo                 
    global digModTxBw                     
    global digModTxAnt                    
    global digModTxCalib                  

    retResult = False

    # Save a new radio configuration file
    ###### settings.py ######
    # localip = "10.0.1.126"
    # rxportno = "5555"
    # txportno = "6666"
    # rxvolume = "15"
    # rxfreq = "446094000"
    # rxsmplrate = "2000000"
    # rxanabw = "5000000"
    # rxdigbw = "100000"
    # rxgain = "10"
    # rxsquelch = "-10"
    # txfreq = "446094000"
    # txsmplrate = "2000000"
    # txanabw = "5000000"
    # txdigbw = "100000"
    # txgain = "60"
    ########################
    # Successfull
    try:
        # Open radio confiuration text file
        files = open("settings.py", "w")

        # Controller local IP address
        tempLocalIP = 'localip = "'
        tempLocalIP = tempLocalIP + localIpAddr + '"\n'
        files.write(tempLocalIP)

        # Controller RX port number
        tempRXPortNo = 'rxportno = "'
        tempRXPortNo = tempRXPortNo + str(rxPortNo) + '"\n'
        files.write(tempRXPortNo)

        # Controller TX port number
        tempTXPortNo = 'txportno = "'
        tempTXPortNo = tempTXPortNo + str(txPortNo) + '"\n'
        files.write(tempTXPortNo)

        # Controller RX audio volume
        tempRXAudio = 'rxvolume = "'
        tempRXAudio = tempRXAudio + str(rxBlckVolume) + '"\n'
        files.write(tempRXAudio)

        # Controller RX center frequency
        tempRXFreq = 'rxfreq = "'
        tempRXFreq = tempRXFreq + str(rxBlckCentFreq) + '"\n'
        files.write(tempRXFreq)

        # Controller RX sample rate
        tempRXSmplRate = 'rxsmplrate = "'
        tempRXSmplRate = tempRXSmplRate + str(rxBlckSmplRate) + '"\n'
        files.write(tempRXSmplRate)

        # Controller RX analog bandwidth
        tempRXAnaBw = 'rxanabw = "'
        tempRXAnaBw = tempRXAnaBw + str(rxBlckBndWidth) + '"\n'
        files.write(tempRXAnaBw)

        # Controller RX digital bandwidth
        tempRXDigBw = 'rxdigbw = "'
        tempRXDigBw = tempRXDigBw + str(rxBlckDigFilt) + '"\n'
        files.write(tempRXDigBw)

        # Controller RX gain
        tempRXgain = 'rxgain = "'
        tempRXgain = tempRXgain + str(rxBlckGain) + '"\n'
        files.write(tempRXgain)

        # Controller RX squelch
        tempRXDsquelch = 'rxsquelch = "'
        tempRXDsquelch = tempRXDsquelch + str(rxBlckSquelch) + '"\n'
        files.write(tempRXDsquelch)

        # Controller TX center frequency
        tempTXFreq = 'txfreq = "'
        tempTXFreq = tempTXFreq + str(txBlckCentFreq) + '"\n'
        files.write(tempTXFreq)

        # Controller TX sample rate
        tempTXSmplRate = 'txsmplrate = "'
        tempTXSmplRate = tempTXSmplRate + str(txBlckSmplRate) + '"\n'
        files.write(tempTXSmplRate)

        # Controller TX analog bandwidth
        tempTXAnaBw = 'txanabw = "'
        tempTXAnaBw = tempTXAnaBw + str(txBlckBndWidth) + '"\n'
        files.write(tempTXAnaBw)

        # Controller TX digital bandwidth
        tempTXDigBw = 'txdigbw = "'
        tempTXDigBw = tempTXDigBw + str(txBlckDigFilt) + '"\n'
        files.write(tempTXDigBw)

        # Controller TX gain
        tempTXgain = 'txgain = "'
        tempTXgain = tempTXgain + str(txBlckGain) + '"\n'
        files.write(tempTXgain)

        # Controller digital modulation center frequency - TX
        tempdigModTxFreq = 'digmodtxfreq = "'
        tempdigModTxFreq = tempdigModTxFreq + str(digModTxFreq) + '"\n'
        files.write(tempdigModTxFreq)

        # Controller digital modulation sample rate - TX
        tempdigModTxSRate = 'digmodtxsrate = "'
        tempdigModTxSRate = tempdigModTxSRate + str(digModTxSRate) + '"\n'
        files.write(tempdigModTxSRate)

        # Controller digital modulation gain - TX
        tempdigModTxGain = 'digmodtxgain = "'
        tempdigModTxGain = tempdigModTxGain + str(digModTxGain) + '"\n'
        files.write(tempdigModTxGain)

        # Controller digital modulation signal source sample rate - TX
        tempdigModTxSSrcSRate = 'digmodtxssrcsrate = "'
        tempdigModTxSSrcSRate = tempdigModTxSSrcSRate + str(digModTxSSrcSRate) + '"\n'
        files.write(tempdigModTxSSrcSRate)

        # Controller digital modulation signal source offset frequency - TX
        tempdigModTxSSrcFOff = 'digmodtxssrcfoff = "'
        tempdigModTxSSrcFOff = tempdigModTxSSrcFOff + str(digModTxSSrcFOff) + '"\n'
        files.write(tempdigModTxSSrcFOff)

        # Controller digital modulation PDU TCP server IP address - TX
        tempdigModTxTcpIp = 'digmodtxtcpip = "'
        tempdigModTxTcpIp = tempdigModTxTcpIp + digModTxTcpIp + '"\n'
        files.write(tempdigModTxTcpIp)

        # Controller digital modulation PDU TCP server port no. - TX
        tempdigModTxTcpPNo = 'digmodtxtcppno = "'
        tempdigModTxTcpPNo = tempdigModTxTcpPNo + digModTxTcpPNo + '"\n'
        files.write(tempdigModTxTcpPNo)

        # Controller digital modulation analog bandwidth - TX
        tempdigModTxBw = 'digmodtxbw = "'
        tempdigModTxBw = tempdigModTxBw + str(digModTxBw) + '"\n'
        files.write(tempdigModTxBw)

        # Controller digital modulation antenna - TX
        tempdigModTxAnt = 'digmodtxant = "'
        tempdigModTxAnt = tempdigModTxAnt + str(digModTxAnt) + '"\n'
        files.write(tempdigModTxAnt)

        # Controller digital modulation calibration - TX
        tempdigModTxCalib = 'digmodtxcalib = "'
        tempdigModTxCalib = tempdigModTxCalib + str(digModTxCalib) + '"\n'
        files.write(tempdigModTxCalib)
        
        # Controller digital modulation center frequency - RX
        tempdigModRxFreq = 'digmodrxfreq = "'
        tempdigModRxFreq = tempdigModRxFreq + str(digModRxFreq) + '"\n'
        files.write(tempdigModRxFreq)

        # Controller digital modulation sample rate - RX
        tempdigModRxSRate = 'digmodrxsrate = "'
        tempdigModRxSRate = tempdigModRxSRate + str(digModRxSRate) + '"\n'
        files.write(tempdigModRxSRate)

        # Controller digital modulation gain - RX
        tempdigModRxGain = 'digmodrxgain = "'
        tempdigModRxGain = tempdigModRxGain + str(digModRxGain) + '"\n'
        files.write(tempdigModRxGain)

        # Controller digital modulation signal source sample rate - RX
        tempdigModRxSSrcSRate = 'digmodrxssrcsrate = "'
        tempdigModRxSSrcSRate = tempdigModRxSSrcSRate + str(digModRxSSrcSRate) + '"\n'
        files.write(tempdigModRxSSrcSRate)

        # Controller digital modulation signal source offset frequency - RX
        tempdigModRxSSrcFOff = 'digmodrxssrcfoff = "'
        tempdigModRxSSrcFOff = tempdigModRxSSrcFOff + str(digModRxSSrcFOff) + '"\n'
        files.write(tempdigModRxSSrcFOff)

        # Controller digital modulation PDU TCP server IP address - RX
        tempdigModRxTcpIp = 'digmodrxtcpip = "'
        tempdigModRxTcpIp = tempdigModRxTcpIp + digModRxTcpIp + '"\n'
        files.write(tempdigModRxTcpIp)

        # Controller digital modulation PDU TCP server port no. - RX
        tempdigModRxTcpPNo = 'digmodrxtcppno = "'
        tempdigModRxTcpPNo = tempdigModRxTcpPNo + digModRxTcpPNo + '"\n'
        files.write(tempdigModRxTcpPNo)

        # Controller digital modulation analog bandwidth - RX
        tempdigModRxBw = 'digmodrxbw = "'
        tempdigModRxBw = tempdigModRxBw + str(digModRxBw) + '"\n'
        files.write(tempdigModRxBw)

        # Controller digital modulation antenna - RX
        tempdigModRxAnt = 'digmodrxant = "'
        tempdigModRxAnt = tempdigModRxAnt + str(digModRxAnt) + '"\n'
        files.write(tempdigModRxAnt)

        # Controller digital modulation calibration - RX
        tempdigModRxCalib = 'digmodrxcalib = "'
        tempdigModRxCalib = tempdigModRxCalib + str(digModRxCalib) + '"\n'
        files.write(tempdigModRxCalib)
                
        # Close the file
        files.close()
        
    # Failed
    except:
        retResult = True
    
    return retResult

# Monitor current radio modulation mode, either analog or digital modulation
# Process voice communication and audio detection
def monitorRadioOperation (threadname, delay):
    global backLogger
    global radioModType
    global restartFlowGraph
    global pttStatusUpdt

    # TX global variables
    global txModType
    global txBlckCentFreq
    global txBlckSmplRate
    global txBlckBndWidth
    global txBlckDigFilt
    global txBlckGain
    global txBlckCFreqUpdt
    global txBlckSmplRUpdt
    global txBlckBWUpdt
    global txBlckDFiltUpdt
    global txBlckGainUpdt
    # RX global variables
    global rxModType
    global rxBlckVolume
    global rxBlckCentFreq
    global rxBlckSmplRate
    global rxBlckBndWidth
    global rxBlckDigFilt
    global rxBlckGain
    global rxBlckSquelch
    global rxBlckVolUpdt
    global rxBlckCFreqUpdt
    global rxBlckSmplRUpdt
    global rxBlckBWUpdt
    global rxBlckGainUpdt
    global rxBlckDFiltUpdt
    global rxBlckSquUpdt
        
    global dummyTxCentFreq
    global dummyTxBpskCentFreq
    global dummyTxBpskSmplRate
    global sendBpskMsgProc
    global digModuReady

    global digModRxFreq                   
    global digModRxSRate                  
    global digModRxGain                   
    global digModRxSSrcSRate
    global digModRxSSrcFOff
    
    global digModTxFreq                   
    global digModTxSRate                  
    global digModTxGain                   
    global digModTxSSrcSRate
    global digModTxSSrcFOff

    global resetPTT
    
    detAudStat = False
    txtProcStat = False
    chkCnt = 0
    currFileRxRetVal = 0.0
    prevFileRxRetVal = 0.0
    currFileTxRetVal = 0.0
    prevFileTxRetVal = 0.0

    top_block_cls = None
    top_block = None
    
    # Fresh restart radio flow graph in digital modulation for text messaging 
    if restartFlowGraph == 2:
        restartFlowGraph = 0

        # Write to logger
        if backLogger == True:
            logger.info("DEBUG_RADIO_OPER: Preparing to start radio TOP-BLOCK in digital modulation mode")
        # Print statement
        else:
            print "DEBUG_RADIO_OPER: Preparing to start radio TOP-BLOCK in digital modulation mode"
                    
        # Initializing block in BPSK modulation 
        top_block_cls = bpsk_messaging
        top_block = top_block_cls()
        
        # Start the BPSK modulation block
        top_block.start()

    # Fresh restart radio flow graph in analog modulation for voice communication
    elif restartFlowGraph == 4:
        restartFlowGraph = 0

        # Write to logger
        if backLogger == True:
            logger.info("DEBUG_RADIO_OPER: Preparing to start radio TOP-BLOCK in analog modulation mode")
        # Print statement
        else:
            print "DEBUG_RADIO_OPER: Preparing to start radio TOP-BLOCK in analog modulation mode"

        # FM transceiver class initialization
        top_block_cls = FM_Transceiver
        top_block = top_block_cls()
    
        # Start the FM transceiver analog modulation block
        top_block.start()
        
    # Radio operation thread loop
    while True:
        time.sleep(delay)

        # Current radio mode - analog modulation, voice operation
        if radioModType == 2:
            chkCnt += 1
            # Every 10s display current radio mode
            if chkCnt == 10:
                chkCnt = 0

                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_RADIO_OPER: Radio transceiver in analog mode - Voice comm")
                # Print statement
                else:
                    print "DEBUG_RADIO_OPER: Radio transceiver in analog mode - Voice comm"

            # Enable PTT for voice transmission - Software control
            if pttStatusUpdt == 3:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_RADIO_OPER: Radio in TRANSCEIVER-TRANSMISSION mode")
                # Print statement
                else:
                    print "DEBUG_RADIO_OPER: Radio in TRANSCEIVER-TRANSMISSION mode"
                    
                # Set the new radio operation mode - Radio in tx mode
                #top_block.set_transmit(0, 446.094e6)
                #top_block.proc_transmit(txBlckCentFreq, dummyRxCentFreq)
                # Volume set to zero
                top_block.proc_transmit(0, txBlckCentFreq)
                
                pttStatusUpdt = 5

            # Disable PTT for receiving voice communication - Software control
            elif pttStatusUpdt == 4:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_RADIO_OPER: Radio in TRANSCEIVER-RECEIVING mode")
                # Print statement
                else:
                    print "DEBUG_RADIO_OPER: Radio in TRANSCEIVER-RECEIVING mode"
                    
                # Set the new radio operation mode - Radio in rx mode
                #top_block.set_receive(10, 0.1)
                #top_block.proc_receive(dummyTxCentFreq, rxBlckCentFreq)
                top_block.proc_receive(rxBlckVolume, dummyTxCentFreq)

                pttStatusUpdt = 6

            # Radio in receiving audio mode  
            else:
                # Checking receive voice audio status
                detAudStat = top_block.get_audiostatus()
                # FM receiver block detects the incoming audio
                if detAudStat == True:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_RADIO_OPER: Incoming AUDIO available")
                    # Print statement
                    else:
                        print "DEBUG_RADIO_OPER: Incoming AUDIO available"

                # FM receiver block NOT detects any incoming audio
                else:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_RADIO_OPER: Incoming AUDIO NOT available")
                    # Print statement
                    else:
                        print "DEBUG_RADIO_OPER: Incoming AUDIO NOT available"

                # Check for any command request
                # Update radio receiver volume value
                if rxBlckVolUpdt == 3:
                    rxBlckVolUpdt = 0
                    # Update radio receiver NEW volume 
                    top_block.set_receive_varVol(rxBlckVolume)

                # Update radio receiver frequency value
                elif rxBlckCFreqUpdt == 3:
                    rxBlckCFreqUpdt = 0

                    # Update radio receiver NEW carrier frequency value 
                    top_block.set_receive_centfreq(rxBlckCentFreq)
                                    
                # Update radio receiver sample rate value
                elif rxBlckSmplRUpdt == 3:
                    rxBlckSmplRUpdt = 0
                    # Update radio receiver NEW sample rate value
                    top_block.set_receive_samplrate(rxBlckSmplRate)

                # Update radio receiver analog filter bandwidth value
                elif rxBlckBWUpdt == 3:
                    rxBlckBWUpdt = 0
                    # Update radio receiver NEW analog filter bandwidth value
                    top_block.set_receive_bndwidth(rxBlckBndWidth)

                # Update radio receiver digital filter bandwidth value
                elif rxBlckDFiltUpdt == 3:
                    rxBlckDFiltUpdt = 0
                    # Update radio receiver NEW digital filter bandwidth value
                    top_block.set_receive_digfilter(rxBlckDigFilt)

                # Update radio receiver gain value
                elif rxBlckGainUpdt == 3:
                    rxBlckGainUpdt = 0
                    # Update radio receiver NEW gain value
                    top_block.set_receive_gain(rxBlckGain)

                # Update radio receiver squelch value
                elif rxBlckSquUpdt == 3:
                    rxBlckSquUpdt = 0
                    # Update radio receiver NEW squelch value
                    top_block.set_receive_varSquelch(rxBlckSquelch)

                # Update radio transmitter frequency value
                elif txBlckCFreqUpdt == 3:
                    txBlckCFreqUpdt = 0

                    # Update radio receiver NEW carrier frequency value
                    top_block.set_transmit_centfreq(txBlckCentFreq)
                    # Reset PTT in the next loop cycle
                    resetPTT = True
                                   
                # Update radio transmitter sample rate value
                elif txBlckSmplRUpdt == 3:
                    txBlckSmplRUpdt = 0
                    # Update radio receiver NEW sample rate value
                    top_block.set_transmit_samplrate(txBlckSmplRate)

                # Update radio transmitter analog filter bandwidth value
                elif txBlckBWUpdt == 3:
                    txBlckBWUpdt = 0
                    # Update radio receiver NEW analog filter bandwidth value
                    top_block.set_transmit_bndwidth(txBlckBndWidth)

                # Update radio transmitter digital filter bandwidth value
                elif txBlckDFiltUpdt == 3:
                    txBlckDFiltUpdt = 3
                    # Update radio receiver NEW digital filter bandwidth value
                    top_block.set_transmit_digfilter(txBlckDigFilt)

                # Update radio transmitter gain value
                elif txBlckGainUpdt == 3:
                    txBlckGainUpdt = 0
                    # Update radio receiver NEW gain value
                    top_block.set_transmit_gain(txBlckGain)

                # Reset back PTT in disable mode
                elif resetPTT == True:
                    resetPTT = False
                    # Reset PTT
                    top_block.proc_receive(rxBlckVolume, dummyTxCentFreq)

        # Current radio mode - BPSK modulation, text messaging
        elif radioModType == 5:
            # Check for enable send text messages transmission flag
            # If enable reconfigure back the carrier frequency
            if sendBpskMsgProc == 1:
                # Resetting back carrier frequency to the actual carrier frequency and sample rate
                #top_block.set_transmit_centfreq(digModTxFreq)
                #top_block.set_transmit_samplrate(digModTxSRate)
                                
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_RADIO_MODE: Resetting back carrier frequency and sample rate for sending text message - Text messaging")
                # Print statement
                else:
                    print "DEBUG_RADIO_MODE: Resetting back carrier frequency and sample rate for sending text message - Text messaging"
                    
                sendBpskMsgProc = 2

            # Check the transmission complex value after multiply operation
            elif sendBpskMsgProc == 3:
                # Check text message transmission status, either already finished or not
                txtProcStat = top_block.get_bpsktxstatus()
                # Text message transmission has finished
                if txtProcStat == True:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_RADIO_MODE: Sending text message process COMPLETED - Text messaging")
                    # Print statement
                    else:
                        print "DEBUG_RADIO_MODE: Sending text message process COMPLETED - Text messaging"

                    txtProcStat = False
                    sendBpskMsgProc = 4

            # Reset back a carrier frequency and sample rate to a dummy value
            elif sendBpskMsgProc == 4:
                # Resetting back carrier frequency to the dummy carrier frequency and sample rate
                #top_block.set_transmit_centfreq(dummyTxBpskCentFreq)
                #top_block.set_transmit_samplrate(dummyTxBpskSmplRate)

                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_RADIO_MODE: Resetting back carrier frequency and sample rate to a dummy value - Text messaging")
                # Print statement
                else:
                    print "DEBUG_RADIO_MODE: Resetting back carrier frequency and sample rate to a dummy value - Text messaging"
                    
                sendBpskMsgProc = 5
            
            chkCnt += 1
            # Every 10s display current radio mode
            if chkCnt == 10:
                chkCnt = 0

                # Set flag for digital modulation are ready
                if digModuReady == 0:
                    digModuReady = 1
                    
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_RADIO_MODE: Radio transceiver in digital mode - Text messaging")
                # Print statement
                else:
                    print "DEBUG_RADIO_MODE: Radio transceiver in digital mode - Text messaging"

        # Initial start - Radio operation are in analog modulation 
        elif radioModType == 0:
            # Initialize radio transceiver block based on the rx and tx flag
            try:
                # Set flag to send current status of radio mode to
                # Node-RED web client - Status: Radio in analog FM transceiver mode
                radioModType = 1
                restartFlowGraph = 3
                
                digModuReady = 0
                chkCnt = 0

                top_block.stop()
                top_block.wait()

                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_RADIO_MODE: Reconfigure to analog FM transceiver mode SUCCESSFULL")
                # Print statement
                else:
                    print "DEBUG_RADIO_MODE: Reconfigure to analog FM transceiver mode SUCCESSFULL"

                # Exit current thread,to restart the radio flow graph in digital modulation 
                break
                    
            # Error during radio block start process
            except:
                 # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_RADIO_MODE: Reconfigure to analog FM transceiver mode FAILED!")
                # Print statement
                else:
                    print "DEBUG_RADIO_MODE: Reconfigure to analog FM transceiver mode FAILED!"
                        
        # Reconfigure radio to BPSK digital mode for text messaging operation
        elif radioModType == 3:
            # Reinitialize back the radio modulation to digital mode
            try:
                # Set flag to send current status of radio mode to
                # Node-RED web client - Status: Radio in digital modulation mode
                radioModType = 4
                restartFlowGraph = 1
                
                top_block.stop()
                top_block.wait()

                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_RADIO_MODE: Reconfigure to BPSK digital mode (text messaging) SUCCESSFULL")
                # Print statement
                else:
                    print "DEBUG_RADIO_MODE: Reconfigure to BPSK digital mode (text messaging) SUCCESSFULL"

                # Exit current thread,to restart the radio flow graph in digital modulation 
                break
            
            # Error during reinitialization
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_RADIO_MODE: Reconfigure to BPSK digital mode (text messaging) FAILED!")
                # Print statement
                else:
                    print "DEBUG_RADIO_MODE: Reconfigure to BPSK digital mode (text messaging) FAILED!"

# TCP client command protocol reply to Node-RED web client
def tcpClientNodeRed (threadname, delay):
    global backLogger
    global localIpAddr
    #################################
    # Radio receiver variables
    #################################
    global rxBlckVolUpdt                  
    global rxBlckCFreqUpdt                
    global rxBlckSmplRUpdt                
    global rxBlckBWUpdt                   
    global rxBlckDFiltUpdt                
    global rxBlckGainUpdt                 
    global rxBlckSquUpdt
    global rxRadioParamUpdt
    #################################
    # Radio transmitter variables
    #################################
    global txBlckCFreqUpdt                
    global txBlckSmplRUpdt                
    global txBlckBWUpdt                   
    global txBlckDFiltUpdt                
    global txBlckGainUpdt                 
    global txRadioParamUpdt
    global txBlckCentFreq 
    global txBlckSmplRate 
    global txBlckBndWidth 
    global txBlckDigFilt 
    global txBlckGain
    #################################
    # Voice operation variables
    #################################
    global voiceOperParamUpdt
    global pttStatusUpdt
    #################################
    # Radio modulation variables
    #################################
    global radioModType
    global restartFlowGraph
    #################################
    global sendBpskMsgProc
    global digModuReady
    
    # Hardcoded port number 
    txPortNumb01 = 6666
    txPortNumb02 = 6667
    txPortNumb03 = 6668
    
    # Process the send command protocol data
    # Protocol structure:[!CMD!TYPE!VALUE!]
    # CMD  : <01>-Radio receiver config, <02>-Radio transmitter config,
    #        <03>-Radio voice operation, <04>-Radio data operation
    #        <05>-Radio RX retrieve conf.<06>-Radio TX retrieve conf.
    #        <19>-Radio voice operation retrieve conf.
    #        <20>-Modulation type
    #        <25>-File transfer
    # TYPE : <01>-Radio receiver volume, <02>-Radio center frequency,
    #        <03>-Radio sampling rate,   <04>-Radio analog filter bandwidth,
    #        <05>-Radio digital filter bandwidth,  <06>-Radio gain,
    #        <07>-Radio squelch          <09>-Radio PTT          
    #        <10>-Radio message          <18>-Retrieve radio parameters
    #        <21>-Analog modulation      <22>-BPSK digital modulation
    #        <26>-File transfer status
    # VALUE: For TYPE:<01>-><07> - Setting process ACK-OK:<13>, ACK-FAILED:<14>
    #        For TYPE:<09> - PTT ON ACK:<15>, PTT OFF ACK:<16>
    #        For TYPE:<10> - Message contents ACK:<17>
    #        For TYPE:<18> - Retrieve all parameters for radio transmitter and receiver
    #        For TYPE:<21> - <NA>
    #        For TYPE:<22> - Text messaging:<23>, File transfer:<24>, Start transmit message: <28>, End transmit message: <29>,
    #                        modulation ready:<30> 
    #        For TYPE:<26> - File transfer completed:<27>
    # Checking loop - check if there is any ACK msg that need to send to node RED web client
    while True:
        time.sleep(delay)
        
        # Send ACK-OK/ACK-FAILED for radio receiver volume setting operation 
        if rxBlckVolUpdt == 1 or rxBlckVolUpdt == 2:
            # Send ACK-OK message to web client
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb02))
                
                # Send the ACK message to web client
                if rxBlckVolUpdt == 1:
                    sock.send("[!01!01!13!]")
                else:
                    sock.send("[!01!01!14!]")
                    
                # Closed the socket
                sock.close()

                if rxBlckVolUpdt == 1:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio receiver volume SET operation-SUCCESFULL, MSG: [!01!01!13!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio receiver volume SET operation-SUCCESFULL, MSG: [!01!01!13!]"
                else:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio receiver volume SET operation-FAILED, MSG: [!01!01!14!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio receiver volume SET operation-FAILED, MSG: [!01!01!14!]"

                #rxBlckVolUpdt = 0
                rxBlckVolUpdt = 3

            # Socket operation failed 
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - RX-Block-Volume")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - RX-Block-Volume"

                # Closed the socket
                sock.close()

        # Send ACK-OK/ACK-FAILED for radio receiver frequency setting operation 
        elif rxBlckCFreqUpdt == 1 or rxBlckCFreqUpdt == 2:
            # Send ACK-OK message to web client
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb02))

                # Send the ACK message to web client
                if rxBlckCFreqUpdt == 1:
                    sock.send("[!01!02!13!]")
                else:
                    sock.send("[!01!02!14!]")
                    
                # Closed the socket
                sock.close()

                if rxBlckCFreqUpdt == 1:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio receiver frequency SET operation-SUCCESFULL, MSG: [!01!02!13!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio receiver frequency SET operation-SUCCESFULL, MSG: [!01!02!13!]"
                else:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio receiver frequency SET operation-FAILED, MSG: [!01!02!14!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio receiver frequency SET operation-FAILED, MSG: [!01!02!14!]"

                #rxBlckCFreqUpdt = 0
                rxBlckCFreqUpdt = 3

            # Socket operation failed 
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - RX-Block-Freq")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - RX-Block-Freq"

                # Closed the socket
                sock.close()
                
        # Send ACK-OK/ACK-FAILED for radio receiver sample rate setting operation
        elif rxBlckSmplRUpdt == 1 or rxBlckSmplRUpdt == 2:
            # Send ACK-OK message to web client
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb02))

                # Send the ACK message to web client
                if rxBlckSmplRUpdt == 1:
                    sock.send("[!01!03!13!]")
                else:
                    sock.send("[!01!03!14!]")
                    
                # Closed the socket
                sock.close()

                if rxBlckSmplRUpdt == 1:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio receiver sample rate SET operation-SUCCESFULL, MSG: [!01!03!13!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio receiver sample rate SET operation-SUCCESFULL, MSG: [!01!03!13!]"
                else:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio receiver sample rate SET operation-FAILED, MSG: [!01!03!14!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio receiver sample rate SET operation-FAILED, MSG: [!01!03!14!]"

                #rxBlckSmplRUpdt = 0
                rxBlckSmplRUpdt = 3

            # Socket operation failed 
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - RX-Block-Sampl.")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - RX-Block-Sampl."

                # Closed the socket
                sock.close()
                
        # Send ACK-OK/ACK-FAILED for radio receiver analog filter BW setting operation
        elif rxBlckBWUpdt == 1 or rxBlckBWUpdt == 2:
            # Send ACK-OK message to web client
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb02))

                # Send the ACK message to web client
                if rxBlckBWUpdt == 1:
                    sock.send("[!01!04!13!]")
                else:
                    sock.send("[!01!04!14!]")
                    
                # Closed the socket
                sock.close()

                if rxBlckBWUpdt == 1:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio receiver analog filter BW SET operation-SUCCESFULL, MSG: [!01!04!13!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio receiver analog filter BW SET operation-SUCCESFULL, MSG: [!01!04!13!]"
                else:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio receiver analog filter BW SET operation-FAILED, MSG: [!01!04!14!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio receiver analog filter BW SET operation-FAILED, [!01!04!14!]"

                #rxBlckBWUpdt = 0
                rxBlckBWUpdt = 3

            # Socket operation failed 
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - RX-Block-Ana.Filt.")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - RX-Block-Ana.Filt."

                # Closed the socket
                sock.close()
                
        # Send ACK-OK/ACK-FAILED for radio receiver digital filter BW setting operation
        elif rxBlckDFiltUpdt == 1 or rxBlckDFiltUpdt == 2:
            # Send ACK-OK message to web client
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb02))

                # Send the ACK message to web client
                if rxBlckDFiltUpdt == 1:
                    sock.send("[!01!05!13!]")
                else:
                    sock.send("[!01!05!14!]")
                    
                # Closed the socket
                sock.close()

                if rxBlckDFiltUpdt == 1:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio receiver digital filter BW SET operation-SUCCESFULL, MSG: [!01!05!13!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio receiver digital filter BW SET operation-SUCCESFULL, MSG: [!01!05!13!]"
                else:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio receiver digital filter BW SET operation-FAILED, MSG: [!01!05!14!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio receiver digital filter BW SET operation-FAILED, MSG: [!01!05!14!]"

                #rxBlckDFiltUpdt = 0
                rxBlckDFiltUpdt = 3

            # Socket operation failed 
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - RX-Block-Dig.Filt.")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - RX-Block-Dig.Filt."

                # Closed the socket
                sock.close()

        # Send ACK-OK/ACK-FAILED for radio receiver gain setting operation
        elif rxBlckGainUpdt == 1 or rxBlckGainUpdt == 2:
            # Send ACK-OK message to web client
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb02))

                # Send the ACK message to web client
                if rxBlckGainUpdt == 1:
                    sock.send("[!01!06!13!]")
                else:
                    sock.send("[!01!06!14!]")
                    
                # Closed the socket
                sock.close()

                if rxBlckGainUpdt == 1:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio receiver gain SET operation-SUCCESFULL, MSG: [!01!06!13!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio receiver gain SET operation-SUCCESFULL, MSG: [!01!06!13!]"
                else:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio receiver gain SET operation-FAILED, MSG: [!01!06!14!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio receiver gain SET operation-FAILED, MSG: [!01!06!14!]"

                #rxBlckGainUpdt = 0
                rxBlckGainUpdt = 3

            # Socket operation failed 
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - RX-Block-Gain")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - RX-Block-Gain"

                # Closed the socket
                sock.close()

        # Send ACK-OK/ACK-FAILED for radio receiver squelch setting operation
        elif rxBlckSquUpdt == 1 or rxBlckSquUpdt == 2:
            # Send ACK-OK message to web client
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb02))

                # Send the ACK message to web client
                if rxBlckSquUpdt == 1:
                    sock.send("[!01!07!13!]")
                else:
                    sock.send("[!01!07!14!]")
                    
                # Closed the socket
                sock.close()

                if rxBlckSquUpdt == 1:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio receiver squelch SET operation-SUCCESFULL, MSG: [!01!07!13!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio receiver squelch SET operation-SUCCESFULL, MSG: [!01!07!13!]"
                else:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio receiver squelch SET operation-FAILED, MSG: [!01!07!14!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio receiver gain squelch operation-FAILED, MSG: [!01!07!14!]"

                #rxBlckSquUpdt = 0
                rxBlckSquUpdt = 3

            # Socket operation failed 
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - RX-Block-Sque.")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - RX-Block-Sque."

                # Closed the socket
                sock.close()

        # Send current stored radio receiver configuration    
        elif rxRadioParamUpdt == True:
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb02))

                # Start construct the radio receiver data
                msgData = '[!05!18!' + str(rxBlckVolume) + '!' + str(rxBlckCentFreq) + '!' + str(rxBlckSmplRate) \
                          + '!' + str(rxBlckBndWidth) + '!' + str(rxBlckDigFilt) + '!' + str(rxBlckGain) \
                          + '!' + str(rxBlckSquelch) + '!]'
                
                sock.send(msgData)
                # Closed the socket
                sock.close()

                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: ACK-Radio receiver retrieve parameters-SUCCESFULL, MSG: %s" % (msgData))
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: ACK-Radio receiver retrieve parameters-SUCCESFULL, MSG: %s" % (msgData)

                rxRadioParamUpdt = False
                
            # Socket operation failed 
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - RX-Block-Stored")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - RX-Block-Stored"

                # Closed the socket
                sock.close()

        # Send ACK-OK/ACK-FAILED for radio transmitter frequency setting operation 
        elif txBlckCFreqUpdt == 1 or txBlckCFreqUpdt == 2:
            # Send ACK-OK message to web client
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb03))

                # Send the ACK message to web client
                if txBlckCFreqUpdt == 1:
                    sock.send("[!02!02!13!]")
                else:
                    sock.send("[!02!02!14!]")
                    
                # Closed the socket
                sock.close()

                if txBlckCFreqUpdt == 1:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio transmitter frequency SET operation-SUCCESFULL, MSG: [!02!02!13!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio transmitter frequency SET operation-SUCCESFULL, MSG: [!02!02!13!]"
                else:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio transmitter frequency SET operation-FAILED, MSG: [!02!02!14!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio transmitter frequency SET operation-FAILED, MSG: [!02!02!14!]"

                #txBlckCFreqUpdt = 0
                txBlckCFreqUpdt = 3

            # Socket operation failed 
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - TX-Block-Freq.")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - TX-Block-Freq."

                # Closed the socket
                sock.close()

        # Send ACK-OK/ACK-FAILED for radio transmitter sample rate setting operation
        elif txBlckSmplRUpdt == 1 or txBlckSmplRUpdt == 2:
            # Send ACK-OK message to web client
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb03))

                # Send the ACK message to web client
                if txBlckSmplRUpdt == 1:
                    sock.send("[!02!03!13!]")
                else:
                    sock.send("[!02!03!14!]")
                    
                # Closed the socket
                sock.close()

                if txBlckSmplRUpdt == 1:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio transmitter sample rate SET operation-SUCCESFULL, MSG: [!02!03!13!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio transmitter sample rate SET operation-SUCCESFULL, MSG: [!02!03!13!]"
                else:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio transmitter sample rate SET operation-FAILED, MSG: [!02!03!14!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio transmitter sample rate SET operation-FAILED, MSG: [!02!03!14!]"

                #txBlckSmplRUpdt = 0
                txBlckSmplRUpdt = 3

            # Socket operation failed 
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - TX-Block-Sampl.")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - TX-Block-Sampl."

                # Closed the socket
                sock.close()

        # Send ACK-OK/ACK-FAILED for radio transmitter analog filter BW setting operation
        elif txBlckBWUpdt == 1 or txBlckBWUpdt == 2:
            # Send ACK-OK message to web client
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb03))

                # Send the ACK message to web client
                if txBlckBWUpdt == 1:
                    sock.send("[!02!04!13!]")
                else:
                    sock.send("[!02!04!14!]")
                    
                # Closed the socket
                sock.close()

                if txBlckBWUpdt == 1:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio transmitter analog filter BW SET operation-SUCCESFULL, MSG: [!02!04!13!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio transmitter analog filter BW SET operation-SUCCESFULL, MSG: [!02!04!13!]"
                else:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio transmitter analog filter BW SET operation-FAILED, MSG: [!02!04!14!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio transmitter analog filter BW SET operation-FAILED, MSG: [!02!04!14!]"

                #txBlckBWUpdt = 0
                txBlckBWUpdt = 3

            # Socket operation failed 
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - TX-Block-Ana.Filt.")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - TX-Block-Ana.Filt."

                # Closed the socket
                sock.close()

        # Send ACK-OK/ACK-FAILED for radio transmitter digital filter BW setting operation
        elif txBlckDFiltUpdt == 1 or txBlckDFiltUpdt == 2:
            # Send ACK-OK message to web client
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb03))

                # Send the ACK message to web client
                if txBlckDFiltUpdt == 1:
                    sock.send("[!02!05!13!]")
                else:
                    sock.send("[!02!05!14!]")
                    
                # Closed the socket
                sock.close()

                if txBlckDFiltUpdt == 1:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio transmitter digital filter BW SET operation-SUCCESFULL, MSG: [!02!05!13!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio transmitter digital filter BW SET operation-SUCCESFULL, MSG: [!02!05!13!]"
                else:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio transmitter digital filter BW SET operation-FAILED, MSG: [!02!05!14!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio transmitter digital filter BW SET operation-FAILED, MSG: [!02!05!14!]"

                #txBlckDFiltUpdt = 0
                txBlckDFiltUpdt = 3

            # Socket operation failed 
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - TX-Block-Dig.Filt.")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - TX-Block-Dig.Filt."

                # Closed the socket
                sock.close()

        # Send ACK-OK/ACK-FAILED for radio transmitter gain setting operation
        elif txBlckGainUpdt == 1 or txBlckGainUpdt == 2:
            # Send ACK-OK message to web client
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb03))

                # Send the ACK message to web client
                if txBlckGainUpdt == 1:
                    sock.send("[!02!06!13!]")
                else:
                    sock.send("[!02!06!14!]")
                    
                # Closed the socket
                sock.close()

                if txBlckGainUpdt == 1:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio transmitter gain SET operation-SUCCESFULL, MSG: [!02!06!13!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio transmitter gain SET operation-SUCCESFULL, MSG: [!02!06!13!]"
                else:
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_NODERED_CLIENT: ACK-Radio transmitter gain SET operation-FAILED, MSG: [!02!06!14!]")
                    # Print statement
                    else:
                        print "DEBUG_NODERED_CLIENT: ACK-Radio transmitter gain SET operation-FAILED, MSG: [!02!06!14!]"

                #txBlckGainUpdt = 0
                txBlckGainUpdt = 3

            # Socket operation failed 
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - TX-Block-Gain")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - TX-Block-Gain"

                # Closed the socket
                sock.close()

        # Send current stored radio transmitter configuration    
        elif txRadioParamUpdt == True:
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb03))

                # Start construct the radio transmitter data
                msgData = '[!06!18!' + str(txBlckCentFreq) + '!' + str(txBlckSmplRate) \
                          + '!' + str(txBlckBndWidth) + '!' + str(txBlckDigFilt) + '!' + str(txBlckGain) + '!]'
                
                sock.send(msgData)
                # Closed the socket
                sock.close()

                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: ACK-Radio transmitter retrieve parameters-SUCCESFULL, MSG: %s" % (msgData))
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: ACK-Radio transmitter retrieve parameters-SUCCESFULL, MSG: %s" % (msgData)

                txRadioParamUpdt = False
                
            # Socket operation failed 
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - TX-Block-Stored")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - TX-Block-Stored"

                # Closed the socket
                sock.close()

        # Send current radio transmitter PTT status - PTT ON 
        elif pttStatusUpdt == 1:
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb01))

                # Start construct the radio transmitter PTT status data
                msgData = '[!03!09!15!]' 
                
                sock.send(msgData)
                # Closed the socket
                sock.close()

                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: ACK-Radio transmitter PTT Status [ON]-SUCCESFULL, MSG: %s" % (msgData))
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: ACK-Radio transmitter PTT Status [ON]-SUCCESFULL, MSG: %s" % (msgData)

                # Trigger radio PTT-ON signal 
                pttStatusUpdt = 3
                
            # Socket operation failed 
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - PTT-ON")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - PTT-ON"

                # Closed the socket
                sock.close()

        # Send current radio transmitter PTT status - PTT OFF
        elif pttStatusUpdt == 2:
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb01))

                # Start construct the radio transmitter PTT status data
                msgData = '[!03!09!16!]' 
                
                sock.send(msgData)
                # Closed the socket
                sock.close()

                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: ACK-Radio transmitter PTT Status [OFF]-SUCCESFULL, MSG: %s" % (msgData))
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: ACK-Radio transmitter PTT Status [OFF]-SUCCESFULL, MSG: %s" % (msgData)

                # Trigger radio PTT-OFF signal 
                pttStatusUpdt = 4
                
            # Socket operation failed 
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - PTT-OFF")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - PTT-OFF"

                # Closed the socket
                sock.close()

        # Send current stored radio receiver configuration    
        elif voiceOperParamUpdt == True:
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb01))

                # Start construct the radio transmitter data
                msgData = '[!19!18!' + str(txBlckCentFreq) + '!' + str(txBlckSmplRate) \
                          + '!' + str(txBlckBndWidth) + '!' + str(txBlckDigFilt) + '!' + str(txBlckGain) + '!]'
                
                sock.send(msgData)
                # Closed the socket
                sock.close()

                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: ACK-Radio transmitter retrieve parameters-SUCCESFULL, MSG: %s" % (msgData))
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: ACK-Radio transmitter retrieve parameters-SUCCESFULL, MSG: %s" % (msgData)

                voiceOperParamUpdt = False
                
            # Socket operation failed 
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - RX-Stored")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - RX-Stored"

                # Closed the socket
                sock.close()

        # Send current radio modulation in analog mode for voice comm
        elif radioModType == 1:
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb01))

                # Start construct current radio modulation in analog mode - voice operation
                msgData = '[!20!21!NA!]' 
                
                sock.send(msgData)
                # Closed the socket
                sock.close()

                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: ACK-Radio modulation (Voice comm.) in analog mode-SUCCESFULL, MSG: %s" % (msgData))
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: ACK-Radio modulation (Voice comm.) in analog mode-SUCCESFULL, MSG: %s" % (msgData)

                radioModType = 2

            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - Radio-Mode-Dig.")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - Radio-Mode-Dig."

                # Closed the socket
                sock.close()
                
        # Send current radio modulation in digital mode for text messaging
        elif radioModType == 4:
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb01))

                # Start construct current radio modulation in digital mode - text messaging
                msgData = '[!20!22!23!]' 
                
                sock.send(msgData)
                # Closed the socket
                sock.close()

                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: ACK-Radio modulation (text messaging) in digital mode-SUCCESFULL, MSG: %s" % (msgData))
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: ACK-Radio modulation (text messaging) in digital mode-SUCCESFULL, MSG: %s" % (msgData)

                radioModType = 5
                
            # Socket operation failed 
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - Radio-Dig.-Text")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - Radio-Dig.-Text"

                # Closed the socket
                sock.close()

        # Send reply for start text message transmission via BPSK modulation 
        elif sendBpskMsgProc == 2:
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb01))

                # Construct ready to START send text message
                msgData = '[!20!22!28!]' 
                
                sock.send(msgData)
                # Closed the socket
                sock.close()

                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: ACK-Request for START text message transmission-SUCCESSFUL, MSG: %s" % (msgData))
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: ACK-Request for START text message transmission-SUCCESSFUL, MSG: %s" % (msgData)

                sendBpskMsgProc = 3
                
            # Socket operation failed 
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - Radio-Dig.-START")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - Radio-Dig.-START"

                # Closed the socket
                sock.close()

        # Send reply status for sending text message to others successfull
        elif sendBpskMsgProc == 5:
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb01))
                
                # Construct END/SUCCESS send text message
                msgData = '[!20!22!29!]' 
                
                sock.send(msgData)
                # Closed the socket
                sock.close()

                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: ACK-Request for END text message transmission-SUCCESSFUL, MSG: %s" % (msgData))
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: ACK-Request for END text message transmission-SUCCESSFUL, MSG: %s" % (msgData)

                sendBpskMsgProc = 0

            # Socket operation failed
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - Radio-Dig.-END/SUCCESS")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - Radio-Dig.-END/SUCCESS"

                # Closed the socket
                sock.close()

        # Send status for digital modulation ready
        elif digModuReady == 1:
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((localIpAddr, txPortNumb01))
                
                # Construct digital modulation ready message
                msgData = '[!20!22!30!]' 
                
                sock.send(msgData)
                # Closed the socket
                sock.close()

                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: ACK-Request for digital modulation ready-SUCCESSFUL, MSG: %s" % (msgData))
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: ACK-Request for digital modulation ready-SUCCESSFUL, MSG: %s" % (msgData)

                digModuReady = 2

            # Socket operation failed
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("DEBUG_NODERED_CLIENT: Socket FAILED! - Radio-Dig.-READY")
                # Print statement
                else:
                    print "DEBUG_NODERED_CLIENT: Socket FAILED! - Radio-Dig.-READY"

                # Closed the socket
                sock.close()
            
# Multithreaded TCP server : TCP Server Socket Thread Pool
class ClientThread(Thread):
    def __init__(self,ip,port):
        global backLogger
        
        Thread.__init__(self) 
        self.ip = ip 
        self.port = port

        # Write to logger
        if backLogger == True:
            # log events, when daemon run in background
            logger.info("DEBUG_CLIENT_THREAD: [+] New server socket thread started for %s:%s" % (ip, str(port)))
        # Print statement
        else:
            print "DEBUG_CLIENT_THREAD: [+] New server socket thread started for %s:%s" % (ip, str(port))

    def run(self):
        global backLogger
        #global top_block
        global localIpAddr
        global rxPortNo
        global backLogger
        global rxBlckVolume 
        global rxBlckCentFreq 
        global rxBlckSmplRate 
        global rxBlckBndWidth 
        global rxBlckDigFilt 
        global rxBlckGain 
        global rxBlckSquelch 
        global txBlckCentFreq 
        global txBlckSmplRate 
        global txBlckBndWidth 
        global txBlckDigFilt 
        global txBlckGain
        global pttStatusUpdt
        global rxBlckVolUpdt                  
        global rxBlckCFreqUpdt                
        global rxBlckSmplRUpdt                
        global rxBlckBWUpdt                   
        global rxBlckDFiltUpdt                
        global rxBlckGainUpdt                 
        global rxBlckSquUpdt                 
        global txBlckCFreqUpdt                
        global txBlckSmplRUpdt                
        global txBlckBWUpdt                   
        global txBlckDFiltUpdt                
        global txBlckGainUpdt
        global rxRadioParamUpdt
        global txRadioParamUpdt
        global clientConn
        global voiceOperParamUpdt
        global radioModType
        global txModType
        global rxModType
        global sendBpskMsgProc
        
        while True:
            # Listen for command protocol data from client
            cmdProtData = clientConn.recv(4096)

            # Write to logger
            if backLogger == True:
                logger.info("DEBUG_TCP_SERVER: Receive command data from client: %s" % (cmdProtData))
            # Print statement
            else:
                print "DEBUG_TCP_SERVER: Receive command data from client: %s" % (cmdProtData)

            # Process the received command protocol data
            # Protocol structure:[!CMD!TYPE!VALUE!]
            # CMD  : <01>-Radio receiver config, <02>-Radio transmitter config,
            #        <03>-Radio voice operation, <04>-Radio data operation
            #        <05>-Radio RX retrieve conf.<06>-Radio TX retrieve conf.
            #        <14>-Radio voice operation retrieve conf.
            #        <15>-Modulation type
            #        <19>-Start file transfer
            #        <20> Messaging
            # TYPE : <01>-Radio receiver volume, <02>-Radio center frequency,
            #        <03>-Radio sampling rate,   <04>-Radio analog filter bandwidth,
            #        <05>-Radio digital filter bandwidth,  <06>-Radio gain,
            #        <07>-Radio squelch          <09>-Radio PTT          
            #        <10>-Radio message          <13>-Retrieve radio parameters
            #        <16>-Messaging (TX) - BPSK modulation
            #        <17>-Analog FM modulation
            #        <18>-File transfer - GMSK modulation
            # VALUE: For TYPE:<01>-><07> - Parameters value
            #        For TYPE:<09> - <11>-PTT ON, <12>-PTT OFF
            #        For TYPE:<10> - <Message contents>
            #        For TYPE:<13> - <NA>
            #        For CMD:<15>,TYPE:<16>&<18> - <NA>
            #        For CMD:<19>,TYPE:<18> - <NA>
            #        For CMD:<20>,TYPE:<16> - <NA> - Start TX the messages
            stx = False
            cmdProtFlag = 0
            exclamCnt = 0
            protCmd = ''
            protType = ''
            protVal = ''
            cmdLen = len(cmdProtData)
            # Go through the command protocol data
            for a in range(0, (cmdLen + 1)):
                oneChar = mid(cmdProtData, a, 1)
                # Search for END command protocol
                if oneChar == ']':
                    break
                # Search for START command protocol
                elif oneChar == '[' and stx == False:
                    stx = True
                # Search the rest of the protocol data 
                elif stx == True:
                    # Search for protocol CMD
                    if cmdProtFlag == 0:
                        if oneChar != '!':
                            protCmd += oneChar
                        else:
                            exclamCnt += 1
                            if exclamCnt == 2:
                                cmdProtFlag = 1
                                exclamCnt = 0

                    # Search for protocol TYPE
                    elif cmdProtFlag == 1:
                        if oneChar != '!':
                            protType += oneChar
                        else:
                            cmdProtFlag = 2

                    # Search for protocol VALUE
                    elif cmdProtFlag == 2:
                        if oneChar != '!':
                            protVal += oneChar

            # Radio receiver config
            if protCmd == '01':
                # Radio receiver volume
                if protType == '01':
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_TCP_SERVER: RX Radio receiver volume: [%s]" % (protVal))
                    # Print statement
                    else:
                        print "DEBUG_TCP_SERVER: RX Radio receiver volume: [%s]" % (protVal)

                    # Update global variable
                    rxBlckVolume = int(protVal)
                    # Update settings.py
                    retResult = updateRadioConfig()
                    # Update config file successfull
                    if retResult == False:
                        # Start update radio receiver block parameter
                        #top_block.set_receive_varVol(rxBlckVolume)
                        # Set status update - SUCCESSFULL
                        rxBlckVolUpdt = 1
                        
                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update RX Radio receiver volume SUCCESSFULL")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update RX Radio receiver volume SUCCESSFULL"

                    # Update config file failed
                    else:
                        # Set status update - FAILED
                        rxBlckVolUpdt = 2

                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update RX Radio receiver volume FAILED!")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update RX Radio receiver volume FAILED!"
                        
                # Radio center frequency
                elif protType == '02':
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_TCP_SERVER: RX Radio center frequency: [%s]" % (protVal))
                    # Print statement
                    else:
                        print "DEBUG_TCP_SERVER: RX Radio center frequency: [%s]" % (protVal)

                    # Update global variable
                    rxBlckCentFreq = int(protVal)
                    # Update settings.py
                    retResult = updateRadioConfig()
                    # Update config file successfull
                    if retResult == False:
                        # Start update radio receiver block parameter
                        #top_block.set_receive_centfreq(rxBlckCentFreq)
                        # Set status update - SUCCESSFULL
                        rxBlckCFreqUpdt = 1
                        
                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update RX Radio receiver frequency SUCCESSFULL")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update RX Radio receiver frequency SUCCESSFULL"

                    # Update config file failed
                    else:
                        # Set status update - FAILED
                        rxBlckCFreqUpdt = 2

                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update RX Radio receiver frequency FAILED!")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update RX Radio receiver frequency FAILED!"

                # Radio sampling rate
                elif protType == '03':
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_TCP_SERVER: RX Radio sampling rate: [%s]" % (protVal))
                    # Print statement
                    else:
                        print "DEBUG_TCP_SERVER: RX Radio sampling rate: [%s]" % (protVal)
                        
                    # Update global variable
                    rxBlckSmplRate = int(protVal)
                    # Update settings.py
                    retResult = updateRadioConfig()
                    # Update config file successfull
                    if retResult == False:
                        # Start update radio receiver block parameter
                        #top_block.set_receive_samplrate(rxBlckSmplRate)
                        # Set status update - SUCCESSFULL
                        rxBlckSmplRUpdt = 1
                        
                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update RX Radio receiver sample rate SUCCESSFULL")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update RX Radio receiver sample rate SUCCESSFULL"

                    # Update config file failed
                    else:
                        # Set status update - FAILED
                        rxBlckSmplRUpdt = 2

                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update RX Radio receiver sample rate FAILED!")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update RX Radio receiver sample rate FAILED!"   
                    
                # Radio analog filter bandwidth
                elif protType == '04':
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_TCP_SERVER: RX Radio analog filter bandwidth: [%s]" % (protVal))
                    # Print statement
                    else:
                        print "DEBUG_TCP_SERVER: RX Radio analog filter bandwidth: [%s]" % (protVal)

                    # Update global variable
                    rxBlckBndWidth = int(protVal)
                    # Update settings.py
                    retResult = updateRadioConfig()
                    # Update config file successfull
                    if retResult == False:
                        # Start update radio receiver block parameter
                        #top_block.set_receive_bndwidth(rxBlckBndWidth)
                        # Set status update - SUCCESSFULL
                        rxBlckBWUpdt = 1
                        
                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update RX Radio receiver analog filter BW SUCCESSFULL")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update RX Radio receiver analog filter BW SUCCESSFULL"

                    # Update config file failed
                    else:
                        # Set status update - FAILED
                        rxBlckBWUpdt = 2

                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update RX Radio receiver analog filter BW FAILED!")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update RX Radio receiver analog filter BW FAILED!" 
                    
                # Radio digital filter bandwidth
                elif protType == '05':
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_TCP_SERVER: RX Radio digital filter bandwidth: [%s]" % (protVal))
                    # Print statement
                    else:
                        print "DEBUG_TCP_SERVER: RX Radio digital filter bandwidth: [%s]" % (protVal)
                        
                    # Update global variable
                    rxBlckDigFilt = int(protVal)
                    # Update settings.py
                    retResult = updateRadioConfig()
                    # Update config file successfull
                    if retResult == False:
                        # Start update radio receiver block parameter
                        #top_block.set_receive_digfilter(rxBlckDigFilt)
                        # Set status update - SUCCESSFULL
                        rxBlckDFiltUpdt = 1
                        
                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update RX Radio receiver digital filter BW SUCCESSFULL")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update RX Radio receiver digital filter BW SUCCESSFULL"

                    # Update config file failed
                    else:
                        # Set status update - FAILED
                        rxBlckDFiltUpdt = 2

                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update RX Radio receiver digital filter BW FAILED!")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update RX Radio receiver digital filter BW FAILED!" 
                    
                # Radio gain
                elif protType == '06':
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_TCP_SERVER: RX Radio gain: [%s]" % (protVal))
                    # Print statement
                    else:
                        print "DEBUG_TCP_SERVER: RX Radio gain: [%s]" % (protVal)

                    # Update global variable
                    rxBlckGain = int(protVal)
                    # Update settings.py
                    retResult = updateRadioConfig()
                    # Update config file successfull
                    if retResult == False:
                        # Start update radio receiver block parameter
                        #top_block.set_receive_gain(rxBlckGain)
                        # Set status update - SUCCESSFULL
                        rxBlckGainUpdt = 1
                        
                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update RX Radio receiver gain SUCCESSFULL")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update RX Radio receiver gain SUCCESSFULL"

                    # Update config file failed
                    else:
                        # Set status update - FAILED
                        rxBlckGainUpdt = 2

                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update RX Radio receiver gain FAILED!")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update RX Radio receiver gain FAILED!" 
                    
                # Radio squelch
                elif protType == '07':
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_TCP_SERVER: RX Radio squelch: [%s]" % (protVal))
                    # Print statement
                    else:
                        print "DEBUG_TCP_SERVER: RX Radio squelch: [%s]" % (protVal)
                        
                    # Update global variable
                    rxBlckSquelch = int(protVal)
                    # Update settings.py
                    retResult = updateRadioConfig()
                    # Update config file successfull
                    if retResult == False:
                        # Start update radio receiver block parameter
                        #top_block.set_receive_varSquelch(rxBlckSquelch)
                        # Set status update - SUCCESSFULL
                        rxBlckSquUpdt = 1
                        
                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update RX Radio receiver squelch SUCCESSFULL")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update RX Radio receiver squelch SUCCESSFULL"

                    # Update config file failed
                    else:
                        # Set status update - FAILED
                        rxBlckSquUpdt = 2

                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update RX Radio squelch FAILED!")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update RX Radio squelch FAILED!"
                
            # Radio transmitter config
            elif protCmd == '02':
                # Radio center frequency
                if protType == '02':
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_TCP_SERVER: TX Radio center frequency: [%s]" % (protVal))
                    # Print statement
                    else:
                        print "DEBUG_TCP_SERVER: TX Radio center frequency: [%s]" % (protVal)

                    # Update global variable
                    txBlckCentFreq = int(protVal)
                    # Update settings.py
                    retResult = updateRadioConfig()
                    # Update config file successfull
                    if retResult == False:
                        # Start update radio transmitter block parameter
                        #top_block.set_transmit_centfreq(txBlckCentFreq)
                        # Set status update - SUCCESSFULL
                        txBlckCFreqUpdt = 1
                        
                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update TX Radio transmitter frequency SUCCESSFULL")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update TX Radio transmitter frequency SUCCESSFULL"

                    # Update config file failed
                    else:
                        # Set status update - FAILED
                        txBlckCFreqUpdt = 2

                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update TX Radio transmitter frequency FAILED!")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update TX Radio transmitter frequency FAILED!"

                # Radio sampling rate
                elif protType == '03':
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_TCP_SERVER: TX Radio sampling rate: [%s]" % (protVal))
                    # Print statement
                    else:
                        print "DEBUG_TCP_SERVER: TX Radio sampling rate: [%s]" % (protVal)
                        
                    # Update global variable
                    txBlckSmplRate = int(protVal)
                    # Update settings.py
                    retResult = updateRadioConfig()
                    # Update config file successfull
                    if retResult == False:
                        # Start update radio transmitter block parameter
                        #top_block.set_transmit_samplrate(txBlckSmplRate)
                        # Set status update - SUCCESSFULL
                        txBlckSmplRUpdt = 1
                        
                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update TX Radio transmitter sample rate SUCCESSFULL")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update TX Radio transmitter sample rate SUCCESSFULL"

                    # Update config file failed
                    else:
                        # Set status update - FAILED
                        txBlckSmplRUpdt = 2

                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update TX Radio transmitter sample rate FAILED!")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update TX Radio transmitter sample rate FAILED!" 

                # Radio analog filter bandwidth
                elif protType == '04':
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_TCP_SERVER: TX Radio analog filter bandwidth: [%s]" % (protVal))
                    # Print statement
                    else:
                        print "DEBUG_TCP_SERVER: TX Radio analog filter bandwidth: [%s]" % (protVal)

                    # Update global variable
                    txBlckBndWidth = int(protVal)
                    # Update settings.py
                    retResult = updateRadioConfig()
                    # Update config file successfull
                    if retResult == False:
                        # Start update radio transmitter block parameter
                        #top_block.set_transmit_bndwidth(txBlckBndWidth)
                        # Set status update - SUCCESSFULL
                        txBlckBWUpdt = 1
                        
                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update TX Radio transmitter analog filter BW SUCCESSFULL")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update TX Radio transmitter analog filter BW SUCCESSFULL"

                    # Update config file failed
                    else:
                        # Set status update - FAILED
                        txBlckBWUpdt = 2

                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update TX Radio transmitter analog filter BW FAILED!")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update RX Radio transmitter analog filter BW FAILED!" 

                # Radio digital filter bandwidth
                elif protType == '05':
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_TCP_SERVER: TX Radio digital filter bandwidth: [%s]" % (protVal))
                    # Print statement
                    else:
                        print "DEBUG_TCP_SERVER: TX Radio digital filter bandwidth: [%s]" % (protVal)
                        
                    # Update global variable
                    txBlckDigFilt = int(protVal)
                    # Update settings.py
                    retResult = updateRadioConfig()
                    # Update config file successfull
                    if retResult == False:
                        # Start update radio transmitter block parameter
                        #top_block.set_transmit_digfilter(txBlckDigFilt)
                        # Set status update - SUCCESSFULL
                        txBlckDFiltUpdt = 1
                        
                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update TX Radio transmitter digital filter BW SUCCESSFULL")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update TX Radio transmitter digital filter BW SUCCESSFULL"

                    # Update config file failed
                    else:
                        # Set status update - FAILED
                        txBlckDFiltUpdt = 2

                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update TX Radio transmitter digital filter BW FAILED!")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update TX Radio transmitter digital filter BW FAILED!" 

                # Radio gain
                elif protType == '06':
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_TCP_SERVER: TX Radio gain: [%s]" % (protVal))
                    # Print statement
                    else:
                        print "DEBUG_TCP_SERVER: TX Radio gain: [%s]" % (protVal)

                    # Update global variable
                    txBlckGain = int(protVal)
                    # Update settings.py
                    retResult = updateRadioConfig()
                    # Update config file successfull
                    if retResult == False:
                        # Start update radio transmitter block parameter
                        #top_block.set_transmit_gain(txBlckGain)
                        # Set status update - SUCCESSFULL
                        txBlckGainUpdt = 1
                        
                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update TX Radio transmitter gain SUCCESSFULL")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update TX Radio transmitter gain SUCCESSFULL"

                    # Update config file failed
                    else:
                        # Set status update - FAILED
                        txBlckGainUpdt = 2

                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Update TX Radio transmitter gain FAILED!")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Update RX Radio transmitter gain FAILED!" 

            # Radio voice operation
            elif protCmd == '03':
                # PTT 
                if protType == '09':
                    # PTT ON
                    if protVal == '11':
                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Radio transmitter operation PTT ON: [%s]" % (protVal))
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Radio transmitter operation PTT ON: [%s]" % (protVal)

                        # Update global variable
                        pttStatusUpdt = 1

                    # PTT OFF
                    elif protVal == '12':
                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Radio transmitter operation PTT OFF: [%s]" % (protVal))
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Radio transmitter operation PTT OFF: [%s]" % (protVal)

                        # Update global variable
                        pttStatusUpdt = 2

            # Radio receiver retrieve current configuration
            elif protCmd == '05':
                # Retrieve radio parameters
                if protType == '13':
                    # Ignore the value
                    if protVal == 'NA':
                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: RX Radio - Retrieve current radio parameters")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: RX Radio - Retrieve current radio parameters"

                        # Set status update - Retrieve radio receiver current parameters
                        rxRadioParamUpdt = True

            # Radio transmitter retrieve current configuration
            elif protCmd == '06':
                # Retrieve radio parameters
                if protType == '13':
                    # Ignore the value
                    if protVal == 'NA':
                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: TX Radio - Retrieve current radio parameters")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: TX Radio - Retrieve current radio parameters"

                        # Set status update - Retrieve radio transmitter current parameters
                        txRadioParamUpdt = True

            # Radio voice operation retrieve current configuration
            elif protCmd == '14':
                # Retrieve radio parameters
                if protType == '13':
                    # Ignore the value
                    if protVal == 'NA':
                        # Write to logger
                        if backLogger == True:
                            logger.info("DEBUG_TCP_SERVER: Radio Voice Operation - Retrieve current radio parameters")
                        # Print statement
                        else:
                            print "DEBUG_TCP_SERVER: Radio Voice Operation - Retrieve current radio parameters"

                        # Set status update - Retrieve radio voice operation current parameters
                        voiceOperParamUpdt = True

            # Enable text messaging using BPSK modulation
            # Messaging (TX) - BPSK modulation
            elif protCmd == '15' and protType == '16':
                # Ignore the value
                if protVal == 'NA':
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_TCP_SERVER: Radio BPSK Operation - Text messaging operation")
                    # Print statement
                    else:
                        print "DEBUG_TCP_SERVER: Radio BPSK Operation - Text messaging operation"

                    # Set a flag for BPSK digital radio for text messaging
                    radioModType = 3

            # Start messaging (TX), initiate carrier frequency - BPSK modulation
            elif protCmd == '20' and protType == '16':
                # Ignore the value
                if protVal == 'NA':
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_TCP_SERVER: Radio BPSK Operation - Start text message transmission")
                    # Print statement
                    else:
                        print "DEBUG_TCP_SERVER: Radio BPSK Operation - Start text message transmission"
                        
                    sendBpskMsgProc = 1

            # Enable FM modulation
            # Analog FM modulation
            elif protCmd == '15' and protType == '17':
                # Ignore the value
                if protVal == 'NA':
                    # Write to logger
                    if backLogger == True:
                        logger.info("DEBUG_TCP_SERVER: Radio FM Operation - Voice operation")
                    # Print statement
                    else:
                        print "DEBUG_TCP_SERVER: Radio FM Operation - Voice operation"

                    # Set a flag for analog FM modulation
                    #radioModType = 1
                    radioModType = 0

# Thread for TCP server - Multi connection connection - Will received command data from node-red web client
def tcpServerMultiClientOperation (threadname, delay):
    global localIpAddr
    global rxPortNo
    global clientConn
    
    # Create a TCP/IP socket
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    # Get the old state of the SO_REUSEADDR option
    old_state = sock.getsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR )

    # Write to logger
    if backLogger == True:
        logger.info("DEBUG_TCP_SERVER: OLD sock state: %s" % old_state)
    # Print statement
    else:
        print "DEBUG_TCP_SERVER: OLD sock state: %s" %old_state
            
    # Enable the SO_REUSEADDR option
    sock.setsockopt( socket.SOL_SOCKET, socket.SO_REUSEADDR, 1 )
    new_state = sock.getsockopt( socket.SOL_SOCKET, socket.SO_REUSEADDR )

    # Write to logger
    if backLogger == True:
        logger.info("DEBUG_TCP_SERVER: NEW sock state: %s" % new_state)
    # Print statement
    else:
        print "DEBUG_TCP_SERVER: NEW sock state: %s" %old_state
            
    # Bind the socket to the port
    server_address = (localIpAddr, rxPortNo)
    
    # Write to logger
    if backLogger == True:
        # log events, when daemon run in background
        logger.info("DEBUG_TCP_SERVER: RX command protocol TCP Server starting up on %s port %s" % server_address)
    # Print statement
    else:
        print "DEBUG_TCP_SERVER: RX command protocol TCP Server starting up on %s port %s" % server_address

    # Create a NEW server socket
    srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    
    # Server bind to IP and port no.
    srv.bind(server_address)
    # Threads array
    threads = []

    # TCP server accept connection loop
    while True:
        time.sleep(delay)

        # Write to logger
        if backLogger == True:
            logger.info("DEBUG_TCP_SERVER: RX command protocol TCP Server waiting for client connection...")
        # Print statement
        else:
            print "DEBUG_TCP_SERVER: RX command protocol TCP Server waiting for client connection..."
            
        # Listen for incoming connections
        srv.listen(4)
        # Accept the client connection    
        (clientConn, (ip,port)) = srv.accept()
        
        newthread = ClientThread(ip,port) 
        newthread.start() 
        threads.append(newthread)

    for t in threads: 
        t.join() 

# FM transceiver class initialization
#top_block_cls=FM_Transceiver
#top_block = top_block_cls()

# Script entry point
def main():
    global radioRxTx
    global backLogger
    global top_block
    global radioRxTxSysChk
    global restartFlowGraph

    global rxBlckCentFreq
    global rxBlckSmplRate
    global rxBlckDigFilt
    global rxBlckGain

    global txBlckCentFreq
    global txBlckSmplRate
    global txBlckDigFilt
    global txBlckGain

    global dummyTxBpskCentFreq
    global dummyTxBpskSmplRate
    
    # Normal operation with hardware PTT switch
    if radioRxTxSysChk == False:
        # Write to logger
        if backLogger == True:
            logger.info("MAIN: Radio in TRANSCEIVER-RECEIVING mode")
        # Print statement
        else:
            print "MAIN: Radio in TRANSCEIVER-RECEIVING mode"

    # Radio receiver-transmitter check
    elif radioRxTxSysChk == True:
        # Write to logger
        if backLogger == True:
            logger.info("MAIN: Radio in RECEIVER-TRANSMITTER CHECK mode")
        # Print statement
        else:
            print "MAIN: Radio in RECEIVER-TRANSMITTER CHECK mode"
            
        # Start thread for radio receiver checking process
        try:
            thread.start_new_thread(radioRxTxCheck, ("[radioRxTxCheck]", 0.5))
        except:
            # Write to logger
            if backLogger == True:
                logger.info("THREAD_ERROR: Unable to start [radioRxTxCheck] thread")
            # Print statement
            else:
                print "THREAD_ERROR: Unable to start [radioRxTxCheck] thread"    

    try:
        thread.start_new_thread(tcpServerMultiClientOperation, ("[tcpServerMultiClientOperation]", 0.1))
    except:
        # Write to logger
        if backLogger == True:
            logger.info("THREAD_ERROR: Unable to start [tcpServerMultiClientOperation] thread")
        # Print statement
        else:
            print "THREAD_ERROR: Unable to start [tcpServerMultiClientOperation] thread"

    try:
        thread.start_new_thread(tcpClientNodeRed, ("[tcpClientNodeRed]", 0.1))
    except:
        # Write to logger
        if backLogger == True:
            logger.info("THREAD_ERROR: Unable to start [tcpClientNodeRed] thread")
        # Print statement
        else:
            print "THREAD_ERROR: Unable to start [tcpClientNodeRed] thread"

    try:
        thread.start_new_thread(monitorRadioOperation, ("monitorRadioOperation", 0.5))
    except:
        # Write to logger
        if backLogger == True:
            logger.info("THREAD_ERROR: Unable to start [monitorRadioOperation] thread")
        # Print statement
        else:
            print "THREAD_ERROR: Unable to start [monitorRadioOperation] thread"
            
    # Main loop
    while True:
        time.sleep(1)

        # Restart radio flow graph for text messaging process
        # The only way to have a process with 2 different modulation
        if restartFlowGraph == 1:
            restartFlowGraph = 2
            try:
                thread.start_new_thread(monitorRadioOperation, ("monitorRadioOperation", 0.5))
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("THREAD_ERROR: Unable to start [monitorRadioOperation] thread")
                # Print statement
                else:
                    print "THREAD_ERROR: Unable to start [monitorRadioOperation] thread"

        # Restart radio flow graph for analog FM transceiver mode
        # The only way to have a process with 2 different modulation
        elif restartFlowGraph == 3:
            restartFlowGraph = 4
            try:
                thread.start_new_thread(monitorRadioOperation, ("monitorRadioOperation", 0.5))
            except:
                # Write to logger
                if backLogger == True:
                    logger.info("THREAD_ERROR: Unable to start [monitorRadioOperation] thread")
                # Print statement
                else:
                    print "THREAD_ERROR: Unable to start [monitorRadioOperation] thread"
            
if __name__ == '__main__':
    main()

