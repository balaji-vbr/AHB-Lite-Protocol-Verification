///////////////////////////////////////////////////////////////////////////////
// Name      : tb.sv : Testbench for AHB lite
// Subject   : Introduction to SystemVerilog [ECE 571]
// Project   : AHB Lite verification
// Authors   : Jonathan Law, Gagan Ganapathy Machiyanda Belliappa, Balaji Rao Vavintaparthi.
// Date      : 11/27/22
// Portland State University
///////////////////////////////////////////////////////////////////////////////


module tb();

import Definitions::*;
`define NoOfSlaves 2

logic                          HCLK, HRESETn, HWRITE, HMASTLOCK, HREADY;
Response_t                     HRESP;
logic   [3:0]                  HPROT;
BType_t                        HBURST;   
Trans_t                        HTRANS;
logic   [DATAWIDTH-1:0]        HWDATA, HRDATA;
logic   [ADDRWIDTH-1:0]        HADDR;
logic   [DATATRANFER_SIZE-1:0] HSIZE;

// Instantiate the DUT
AHB_TOP DUT (
    .HCLK       (HCLK),
    .HRESETn    (HRESETn),
    .HWDATA     (HWDATA),
    .HADDR      (HADDR),
    .HSIZE      (HSIZE),
    .HBURST     (HBURST),
    .HTRANS     (HTRANS),
    .HWRITE     (HWRITE),
    .HMASTLOCK	(HMASTLOCK),
    .HREADY     (HREADY),
    .HPROT      (HPROT),
    .HRDATA     (HRDATA),
    .HRESP      (HRESP)
);  

/* Verification plan
Transfer types
 - burst 4,8,16
 - incr and wrap
 - write and read

Signals in memcontroller
 - Tested - HCLK, HRESETn, HADDR, HWDATA, HRDATA, HWRITE, HTRANS, HBURST, HREADY
 - Constant - HSIZE
 - Not utilized - HPROT, HMASTLOCK

*/

// clock and reset generator
initial begin
	HCLK = 0;
	HRESETn = 1'b1;
    
	HRESETn <= #0 1'b0;
	$display("reset");
	HRESETn <= #5 1'b1;
    
	forever #5 HCLK = ~HCLK;
end

// packet transfer initialization
task transfer_init(
    input write,
    Trans_t transfer=NONSEQ,
    BType_t burst=SINGLE,
    input [2:0] size=3'b000,
    input [3:0] prot=4'b0011,
    input lock=0,
    input ready=1
);
    $display("TB::set: write: %b transfer: %s burst: %s size: %03b prot: %04b lock: %d ready: %d",
            write, transfer.name, burst.name, size, prot, lock, ready);
    HWRITE    = write;
    HTRANS    = transfer;
    HBURST    = burst;
    HSIZE     = size;
    HPROT     = prot;
    HMASTLOCK = lock;
    HREADY    = ready;
endtask
task addr_op(input [ADDRWIDTH-1:0] addr);
    $display("TB::addr: %h",addr);
    HADDR  = addr;
    @(posedge HCLK);
endtask
task write_op(input [DATAWIDTH-1:0] data);
    $display("TB::write, data: %h",data);
    HWDATA = data;
    @(posedge HCLK);
endtask
task read_op(output [DATAWIDTH-1:0] data);
    @(posedge HCLK);
    data = HRDATA;
    $display("TB::read, data: %h",data);
endtask
task packet(
    input [ADDRWIDTH-1:0] addr,
    input [DATAWIDTH-1:0] wdata[],
    output [DATAWIDTH-1:0] rdata[16],
    input write,
    Trans_t transfer=NONSEQ,
    BType_t burst=SINGLE,
    input [2:0] size=3'b000,
    input [3:0] prot=4'b0011,
    input lock=0,
    input ready=1
);
    integer N;
    // logic [DATAWIDTH-1:0] rdata[16];
    integer bsize;
    bsize = (ADDRWIDTH'('b1) << size);
    N = ((burst==WRAP4) | (burst==INCR4)) ? 4 :
        ((burst==WRAP8) | (burst==INCR8)) ? 8 :
        ((burst==WRAP16) | (burst==INCR16)) ? 16 :
        1;
    
    $display("\n@packet",N);
    transfer_init(write, NONSEQ, burst, size, prot, lock, ready);
    addr_op(addr);
    
    transfer_init(write, SEQ, burst, size, prot, lock, ready);
    for (int i=0; i<N; i++) begin
        if (HWRITE)
            write_op(wdata[i]);
        else
            read_op(rdata[i]);
    end
    transfer_init(write, IDLE, burst, size, prot, lock, !ready);
    @(posedge HCLK);
    
endtask

`define TEST_WRAP(N,A)\
addr = ADDRWIDTH'(A);\
packet(addr,wdata,rdata, 1, .burst(WRAP``N));\
$display("%p",DUT.slave1.m1.M[HADDR-(HADDR%N)+:N]);\
packet(addr,wdata,rdata, 0, .burst(WRAP``N));\
$display("%p",DUT.slave1.m1.M[HADDR-(HADDR%N)+:N]);\
$display("Start: %h, Wrap: %h",A,A-(A%N));\
$display("%p === %p",wdata[0:N-1], rdata[0:N-1]);\
assert(wdata[0:N-1] === rdata[0:N-1]) $display("PASS"); else $display("FAIL");

`define TEST_INCR(N,A)\
addr = ADDRWIDTH'(A);\
packet(addr,wdata,rdata, 1, .burst(INCR``N));\
$display("%p",DUT.slave1.m1.M[HADDR+:N]);\
packet(addr,wdata,rdata, 0, .burst(INCR``N));\
$display("%p",DUT.slave1.m1.M[HADDR+:N]);\
$display("%p === %p",wdata[0:N-1], rdata[0:N-1]);\
assert(wdata[0:N-1] === rdata[0:N-1]) $display("PASS"); else $display("FAIL");

// test sequence
logic [ADDRWIDTH-1:0] addr;
logic [DATAWIDTH-1:0] wdata[16],rdata[16];
initial begin
    $display("\ntest sequence\n");
    #1
    @(posedge HRESETn)
    $display("\ntest start\n");
    
    for (int i=0; i<16; i++) begin
        wdata[i] = SLAVE_DATAWIDTH'($urandom);
    end
    
    `TEST_WRAP(4,'ha6);
    `TEST_INCR(4,'hb6);
    `TEST_WRAP(8,'hc6);
    `TEST_INCR(8,'hd6);
    `TEST_WRAP(16,'h36);
    `TEST_INCR(16,'h66);
    
    addr = ADDRWIDTH'('h6);
    packet(addr,wdata,rdata, 1, .burst(SINGLE));
    $display("%p",DUT.slave1.m1.M[HADDR+:1]);
    packet(addr,wdata,rdata, 0, .burst(SINGLE));
    $display("%p",DUT.slave1.m1.M[HADDR+:1]);
    $display("%p === %p",wdata[0:1-1], rdata[0:1-1]);
    assert(wdata[0:1-1] === rdata[0:1-1]) $display("PASS"); else $display("FAIL");
    
    addr = ADDRWIDTH'('h16);
    packet(addr,wdata,rdata, 1, .burst(INCR));
    $display("%p",DUT.slave1.m1.M[HADDR+:1]);
    packet(addr,wdata,rdata, 0, .burst(INCR));
    $display("%p",DUT.slave1.m1.M[HADDR+:1]);
    $display("%p === %p",wdata[0:1-1], rdata[0:1-1]);
    assert(wdata[0:1-1] === rdata[0:1-1]) $display("PASS"); else $display("FAIL");
    
    
    
    $display("\ntest stop\n");
    #10 $stop;
end


`define ASSERT_BURST(N) \
sequence burst``N ;\
 HTRANS == NONSEQ ##1  HTRANS == SEQ[*(N-1)];\
endsequence \
property assert_burst``N;\
 @(posedge HCLK) disable iff (!HRESETn)   \
 (((HBURST == INCR``N) || (HBURST ==WRAP``N))\
 ##[0:(N-1)] \
 ((HTRANS != BUSY) || (HTRANS != IDLE))) \
 |->  burst``N;  \
endproperty 

`ASSERT_BURST(4);
`ASSERT_BURST(8);
`ASSERT_BURST(16);

assert_b4: assert property (assert_burst4);
assert_b8: assert property (assert_burst8);
assert_b16: assert property (assert_burst16);


//////////////////////////Assertions////////////////////////////////////////////

//property error_check;
//@(posedge HCLK) disable iff (HTRANS == BUSY || HTRANS == IDLE)
//(HADDR > ((2**10)* `NoOfSlaves))|-> (HRESP == 1'b1); 
//endproperty

//assert property(error_check);
//error_check_Pass++;
//else
//error_check_Fail++;

//Checks whether the address is in the Read only Memory of Slave,in our case we have considered 1st three address as ROM
//property  read_only_error_check;
//@(posedge HCLK) disable iff ( (HADDR[9:0] > 9'd3))
 //(HWRITE == 1'b1) |=> (HRESP == 1);
//endproperty

//assert property(read_only_error_check);
//read_only_error_check_Pass++;
//else
//read_only_error_check_Fail++;

//assertion- for basic write -> hwrite is detected high at the 2nd clk,at the third clk,hready goes high
property basic_write;
@(posedge HCLK) disable iff ((HTRANS==IDLE || HTRANS==BUSY) && HBURST>'0) $rose(HWRITE) |=> HREADY;
endproperty

assert property(basic_write);
//basic_write_Pass++; 
//else 
//basic_write_Fail++;

//assertion- for basic read -> hwrite is detected low at the 2nd clk,at the third clk,hready goes high
property basic_read;
@(posedge HCLK) disable iff ((HTRANS==IDLE || HTRANS==BUSY) && HBURST>'0 || (HADDR > ((2**10)* `NoOfSlaves))) $fell(HWRITE) |=> HREADY;
endproperty

assert property(basic_read);
//basic_read_Pass++; 
//else  
//basic_read_Fail++;


// assertion- for burst write -> hwrite is detected high & htrans is in non sequential state at the 2nd clk,at the third clk,hready goes high,disabled if it is busy in state.
property basic_burst_write;
@(posedge HCLK) disable iff (HTRANS == BUSY)
((HWRITE==1)&&(HTRANS == NONSEQ) )|=>	(HREADY=='1) ;
endproperty

assert property(basic_burst_write);
//basic_burst_write_Pass++; 
//else  
//basic_burst_write_Fail++;


// assertion- for burst write -> hwrite is detected low & htrans is in non sequential state at the 2nd clk,at the third clk,hready goes high,disabled if it is busy in busy state.
property basic_burst_read;
@(posedge HCLK) disable iff (HTRANS == BUSY || (HADDR > ((2**10)* `NoOfSlaves)))
((HWRITE=='0)&&(HTRANS == NONSEQ) )|=>	(HREADY=='1) ;
endproperty

assert property(basic_burst_read);
//basic_burst_read_Pass++; 
//else  
//basic_burst_read_Fail++;

// assertion for - non_seq to seq transition
property seq_Check;
@(posedge HCLK) (( (HWRITE=='1) || (HWRITE=='0) ) && (HTRANS==NONSEQ) ) |=> (HTRANS == SEQ);
endproperty

assert property(seq_Check);
//seq_check_Pass++;
//else
//seq_check_Fail++;

//assertion for HREADY -if HREADY is low then HADDR and HWRITE and HWDATA should remain in the same state until it HREADY goes high.
property HREADY_Check;
@(posedge HCLK) (HREADY == 1'b0) |=> $stable (HADDR && HWRITE && HWDATA) ;
endproperty

assert property(HREADY_Check);
//HREADY_check_Pass++;
//else
//HREADY_check_Fail++;

//checks for 4 incrementing bursts whether the state transitions is going on properly,i.e. non-sequential followed by 3 sequential states
property burst_count_check4;                                     
@(posedge HCLK) disable iff(HTRANS == BUSY || HBURST !=3'b011)  
(HTRANS == 2'b10) |=> (HTRANS == SEQ)|=> (HTRANS == SEQ)[*2];
endproperty

assert property(burst_count_check4);
//burstcount_check4_Pass++;
//else
//burstcount_check4_Fail++;

//checks for 8 incrementing bursts whether the state transitions is going on properly,i.e. non-sequential followed by 7 sequential states
property burst_count_check8;                                
@(posedge HCLK)disable iff(HTRANS == BUSY || HBURST !=3'b101) 
(HTRANS == NONSEQ) |=> (HTRANS == SEQ)|=> (HTRANS == SEQ)[*7];
endproperty

assert property(burst_count_check8);
//burstcount_check8_Pass++;
//else
//burstcount_check8_Fail++;

//checks for 16 incrementing bursts whether the state transitions is going on properly,i.e. non-sequential followed by 15 sequential states
property burst_count_check16;      
@(posedge HCLK)disable iff(HTRANS == BUSY  || HBURST !=3'b111) 
(HTRANS == NONSEQ) |=> (HTRANS == SEQ) |=> (HTRANS == SEQ)[*14];
endproperty

assert property(burst_count_check16);
//burstcount_check16_Pass++;
//else
//burstcount_check16_Fail++;

//checks for 4 incrementing bursts whether the address change is happening over period of next 3 clock cycles
property address_change4;
@(posedge HCLK) disable iff (HBURST!=3'b011)
(HTRANS == NONSEQ) |=> not ($stable(HADDR)[*3]);
endproperty

assert property(address_change4);
//address_change4_Pass++;
//else
//address_change4_Fail++;

//checks for 8 incrementing bursts whether the address change is happening over period of next 7 clock cycles 
property address_change8;
@(posedge HCLK) disable iff (HBURST!=3'b101)
(HTRANS == NONSEQ) |=> not ($stable(HADDR)[*7]); 
endproperty

assert property(address_change8);
//address_change8_Pass++;
//else
//address_change8_Fail++;

//checks for 16 incrementing bursts whether the address change is happening over period of next 15 clock cycles 
property address_change16;
@(posedge HCLK) disable iff (HBURST!=3'b111)
(HTRANS == NONSEQ) |=> not ($stable(HADDR)[*15]); 
endproperty

assert property(address_change16);
//address_change16_Pass++;
//else
//address_change16_Fail++;


endmodule