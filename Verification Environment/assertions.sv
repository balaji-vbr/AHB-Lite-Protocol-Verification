///////////////////////////////////////////////////////////////////////////////
// Name      : assertions.sv
// Subject   : Introduction to SystemVerilog [ECE 571]
// Project   : AHB Lite verification
// Authors   : Jonathan Law, Gagan Ganapathy Machiyanda Belliappa, Balaji Rao Vavintaparthi.
// Date      : 11/27/22
// Portland State University
///////////////////////////////////////////////////////////////////////////////
import Definitions::*;				

module scoreboard(AHBInterface Bus,
               input logic reset);

`define NoOfSlaves 2

integer basic_write_Pass,basic_write_Fail;
integer basic_read_Pass,basic_read_Fail;
integer basic_burst_write_Pass,basic_burst_write_Fail;
integer basic_burst_read_Pass,basic_burst_read_Fail;
integer seq_check_Pass,seq_check_Fail;
integer HREADY_check_Pass,HREADY_check_Fail;
integer burstcount_check4_Pass,burstcount_check4_Fail;
integer burstcount_check8_Pass,burstcount_check8_Fail;
integer burstcount_check16_Pass,burstcount_check16_Fail;
integer address_change4_Pass,address_change4_Fail;
integer address_change8_Pass,address_change8_Fail;
integer address_change16_Pass,address_change16_Fail;



//assertion- for basic write -> hwrite is detected high at the 2nd clk,at the third clk,hready goes high
property basic_write;
	@(posedge Bus.HCLK) disable iff ((Bus.HTRANS==IDLE || Bus.HTRANS==BUSY) && Bus.HBURST>'0) $rose(Bus.HWRITE) |=> Bus.HREADY;
endproperty

assert property(basic_write)
basic_write_Pass++; 
else 
basic_write_Fail++;

//assertion- for basic read -> hwrite is detected low at the 2nd clk,at the third clk,hready goes high
property basic_read;
	@(posedge Bus.HCLK) disable iff ((Bus.HTRANS==IDLE || Bus.HTRANS==BUSY) && Bus.HBURST>'0 || (Bus.HADDR > ((2**10)* `NoOfSlaves))) $fell(Bus.HWRITE) |=> Bus.HREADY;
endproperty

assert property(basic_read)
basic_read_Pass++; 
else  
basic_read_Fail++;


// assertion- for burst write -> hwrite is detected high & htrans is in non sequential state at the 2nd clk,at the third clk,hready goes high,disabled if it is busy in state.
property basic_burst_write;
@(posedge Bus.HCLK) disable iff (Bus.HTRANS == BUSY)
((Bus.HWRITE==1)&&(Bus.HTRANS == NON_SEQ) )|=>	(Bus.HREADY=='1) ;
endproperty

assert property(basic_burst_write)
basic_burst_write_Pass++; 
else  
basic_burst_write_Fail++;


// assertion- for burst write -> hwrite is detected low & htrans is in non sequential state at the 2nd clk,at the third clk,hready goes high,disabled if it is busy in busy state.
property basic_burst_read;
@(posedge Bus.HCLK) disable iff (Bus.HTRANS == BUSY || (Bus.HADDR > ((2**10)* `NoOfSlaves)))
((Bus.HWRITE=='0)&&(Bus.HTRANS == NON_SEQ) )|=>	(Bus.HREADY=='1) ;
endproperty

assert property(basic_burst_read)
basic_burst_read_Pass++; 
else  
basic_burst_read_Fail++;

// assertion for - non_seq to seq transition
property seq_Check;
@(posedge Bus.HCLK) (( (Bus.HWRITE=='1) || (Bus.HWRITE=='0) ) && (Bus.HTRANS==NON_SEQ) ) |=> (Bus.HTRANS == SEQ);
endproperty

assert property(seq_Check)
seq_check_Pass++;
else
seq_check_Fail++;

//assertion for HREADY -if HREADY is low then HADDR and HWRITE and HWDATA should remain in the same state until it HREADY goes high.
property HREADY_Check;
@(posedge Bus.HCLK) (Bus.HREADY == 1'b0) |=> $stable (Bus.HADDR && Bus.HWRITE && Bus.HWDATA) ;
endproperty

assert property(HREADY_Check)
HREADY_check_Pass++;
else
HREADY_check_Fail++;

//checks for 4 incrementing bursts whether the state transitions is going on properly,i.e. non-sequential followed by 3 sequential states
property burst_count_check4;                                     
@(posedge Bus.HCLK) disable iff(Bus.HTRANS == BUSY || Bus.HBURST !=3'b011)  
(Bus.HTRANS == 2'b10) |=> (Bus.HTRANS == SEQ)|=> (Bus.HTRANS == SEQ)[*2];
endproperty

assert property(burst_count_check4)
burstcount_check4_Pass++;
else
burstcount_check4_Fail++;

//checks for 8 incrementing bursts whether the state transitions is going on properly,i.e. non-sequential followed by 7 sequential states
property burst_count_check8;                                
@(posedge Bus.HCLK)disable iff(Bus.HTRANS == BUSY || Bus.HBURST !=3'b101) 
(Bus.HTRANS == NON_SEQ) |=> (Bus.HTRANS == SEQ)|=> (Bus.HTRANS == SEQ)[*7];
endproperty

assert property(burst_count_check8)
burstcount_check8_Pass++;
else
burstcount_check8_Fail++;

//checks for 16 incrementing bursts whether the state transitions is going on properly,i.e. non-sequential followed by 15 sequential states
property burst_count_check16;      
@(posedge Bus.HCLK)disable iff(Bus.HTRANS == BUSY  || Bus.HBURST !=3'b111) 
(Bus.HTRANS == NON_SEQ) |=> (Bus.HTRANS == SEQ) |=> (Bus.HTRANS == SEQ)[*14];
endproperty

assert property(burst_count_check16)
burstcount_check16_Pass++;
else
burstcount_check16_Fail++;

//checks for 4 incrementing bursts whether the address change is happening over period of next 3 clock cycles
property address_change4;
@(posedge Bus.HCLK) disable iff (Bus.HBURST!=3'b011)
(Bus.HTRANS == NON_SEQ) |=> not ($stable(Bus.HADDR)[*3]);
endproperty

assert property(address_change4)
address_change4_Pass++;
else
address_change4_Fail++;

//checks for 8 incrementing bursts whether the address change is happening over period of next 7 clock cycles 
property address_change8;
@(posedge Bus.HCLK) disable iff (Bus.HBURST!=3'b101)
(Bus.HTRANS == NON_SEQ) |=> not ($stable(Bus.HADDR)[*7]); 
endproperty

assert property(address_change8)
address_change8_Pass++;
else
address_change8_Fail++;

//checks for 16 incrementing bursts whether the address change is happening over period of next 15 clock cycles 
property address_change16;
@(posedge Bus.HCLK) disable iff (Bus.HBURST!=3'b111)
(Bus.HTRANS == NON_SEQ) |=> not ($stable(Bus.HADDR)[*15]); 
endproperty

assert property(address_change16)
address_change16_Pass++;
else
address_change16_Fail++;

endmodule