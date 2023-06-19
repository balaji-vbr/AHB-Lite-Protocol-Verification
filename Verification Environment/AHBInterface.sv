///////////////////////////////////////////////////////////////////////////////
// Name      : AHBInterface.sv 
// Subject   : Introduction to SystemVerilog [ECE 571]
// Project   : AHB Lite verification
// Authors   : Jonathan Law, Gagan Ganapathy Machiyanda Belliappa, Balaji Rao Vavintaparthi.
// Date      : 
// Portland State University
///////////////////////////////////////////////////////////////////////////////







import Definitions::*;				


interface AHBInterface(input HCLK,input HRESETn);

	
	logic [ADDRESS_WIDTH-1:0] 	HADDR;
	logic 				  		HWRITE;
	logic [HSIZE_WIDTH-1:0]		HSIZE;
	logic [BURST_SIZE-1:0]		HBURST;
	logic [TRANSFER_TYPE-1:0]	HTRANS;
	logic [DATA_WIDTH-1:0]		HWDATA;
	logic [DATA_WIDTH-1:0]		HRDATA;
	logic						HREADY;
	logic						HRESP;
	bit [ADDRESS_WIDTH-1:0] 	ADDR;
	int	i,j,k,n;
	int count=0;
		
	
/////////////////////////////////////////////////BASIC READ WITH AND WITHOUT WAIT STATES/////////////////////////////////////////////
	
task read(input bit [ADDRESS_WIDTH-1:0] addr, output logic [DATA_WIDTH-1:0] data);
	@(posedge HCLK);
	HADDR 	= addr;									// Address put on the Address bus
	HWRITE 	= '0;									// Indicates that this is a read operation
	HSIZE	= 3'b010;								// define HSIZE as a Parameter and change it in compile time
	HBURST	= 3'b000;								// Single burst

	if (HRESP)		$display (" Error response from SLAVE to MASTER \n ");
	while (!HREADY);	

	@(posedge HCLK);
	@(posedge HCLK);
	data = HRDATA;  								
endtask


task burst_read (bit [ADDRESS_WIDTH-1:0] addr,  input int BEATS, input int busy, output bit [DATA_WIDTH-1:0] data_burst4[31:0]);
	automatic int i,j=0;
	@(posedge HCLK);
	HADDR = addr;
	HTRANS = NON_SEQ;
	HWRITE = 1'b0;
	@(posedge HCLK);
	`ifndef ERROR_INJECT
	HADDR = addr +1;
	`endif
	repeat(busy) begin
		j++;
		HTRANS = BUSY;
		@(posedge HCLK);
		if(j == busy) HTRANS = SEQ;
	end
	
	i=0;
        repeat(BEATS-2) begin
                @(posedge HCLK);
                HADDR = HADDR + 1;
				`ifndef ERROR_INJECT
				HTRANS = SEQ;
				`endif
                data_burst4[i] = HRDATA;
                i=i+1;
        end
        @(posedge HCLK);
        data_burst4[i] = HRDATA;
        i=i+1;
        @(posedge HCLK);
        data_burst4[i] = HRDATA;
	
endtask



	
/////////////////////////////////////////////////BASIC WRITE TASK WITH AND WITHOUT WAIT STATES/////////////////////////////////////////////

task write(input bit[ADDRESS_WIDTH-1:0] addr, input logic[DATA_WIDTH-1:0] data);	
	@(posedge HCLK);
	HADDR 	= addr;									// Address put on the Address bus
	HWRITE 	= '1;									// indicates that this is a write operation
	HSIZE	= 3'b010;	
	HBURST 	= '0;									//	signifies that it is a single burst
	while (!HREADY); 
	@(posedge HCLK);
	`ifndef ERROR_INJECT
	HWDATA	= data;
	`endif
	@(posedge HCLK);
	if (HRESP)		$display ("Error - writing to read only memory not allowed \n");	
endtask	




/////////////////////////////////////////////////BURST 4 BEAT BURST WRITE TASK WITH AND WITHOUT BUSY STATES/////////////////////////////////////////////

task burst_write (bit[ADDRESS_WIDTH-1:0] addr,  input int BEATS, input int busy, input bit[DATA_WIDTH-1:0] data4[31:0]);
	if (BEATS == 4) 	HBURST 	= 3'b011;				//	signifies that it is a burst of length 4
	if (BEATS == 8)		HBURST	= 3'b101;				//	signifies that it is a burst of length 8
	if (BEATS == 16)	HBURST	= 3'b111;				//	signifies that it is a burst of length 16
	i=0;
	k=0;
	j=0;
	if (HRESP)		$display ("Error\n");
	fork
		begin
		repeat (BEATS)
			begin
			if (i==0)			HTRANS = NON_SEQ;
			HADDR = addr;
			`ifndef ERROR_INJECT
			HWRITE 	= 1;
			`endif
			@(posedge HCLK);
			HADDR = addr;
			while (!HREADY); 
			addr = addr+1;
			i=i+1;	
			if (busy ==32'd1)
				begin
				if (i==2)
					begin
					HTRANS = BUSY;
					@(posedge HCLK);
					end
				end
			
			if (busy == 32'd2)
				begin
				if (i==3)
					begin
					HTRANS = BUSY;
					@(posedge HCLK);
					@(posedge HCLK);
					end
				end
				
			if ( (busy==32'd1)||(busy ==32'd2) )	
				begin
				if ((i!=2) || (i!=3))
					HTRANS = BUSY;
				end
				else
				begin
					//`ifndef ERROR_INJECT
					HTRANS = SEQ; 
					//`endif
				end
				end
		end
		
		begin
		repeat (BEATS)
			begin
			@(posedge HCLK);
			HWDATA = data4[j];
			while (!HREADY);
			j=j+1;
			k = k+1;
			if (busy ==32'd1)
				begin
				if (k==2)
					begin
					@(posedge HCLK);
					end
				end
			
			if (busy == 32'd2)
				begin
				if (k==3)
					begin
					@(posedge HCLK);
					@(posedge HCLK);
					end
				end
			end
		end
	join
endtask



//////////////////////////////////////////////// MODPORT FOR SLAVE ////////////////////////////////////////////////////
	
modport Slave(
					output HREADY,
					output HRESP,
					output HRDATA,
					input HADDR,
					input HWRITE,
					input HSIZE,
					input HBURST,
					input HTRANS,
					input HWDATA,
					input HCLK,
					input HRESETn
	);
					
//////////////////////////////////////////////// MODPORT FOR MASTER ////////////////////////////////////////////////////
	
modport Master(
      	input 		HCLK,
      	input  		HRESETn,
      	output 		HSEL,HADDR,HWDATA,HWRITE,HRDATA,HSIZE,HBURST,HPROT,HTRANS,HREADY,
	    input 		HREADYOUT,HRESP
  );

					
endinterface