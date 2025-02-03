// //----------------------------------------------Detect Sequence----------------------------------------------//
module detect_sequence(
    input clk, rst_n,
    input data_in,
    output valid
);
    localparam  init = 6'b000001,
                S1 = 6'b000010,
                S01 = 6'b000100,
                S101 = 6'b001000,
                S1101 = 6'b010000,
                S01101 = 6'b100000;

    logic [5:0] currentState, nextState;
    
    // State memory
    always_ff @(posedge clk or negedge rst_n) begin : MemoryState
        if(!rst_n) begin
            currentState <= init;
        end
        else begin
            currentState <= nextState;
        end
    end

    // Next State Logic
    always_comb begin : NextState
        case(currentState)
            init: begin
                if(data_in) nextState = S1;
                else nextState = init;
            end
            S1: begin
                if(data_in) nextState = S1;
                else nextState = S01;
            end 
            S01: begin
                if(data_in) nextState = S101;
                else nextState = init;
            end
            S101: begin
                if(data_in) nextState = S1101;
                else nextState = S01;
            end
            S1101: begin
                if(data_in) nextState = S1;
                else nextState = S01101;
            end
            S01101: begin
                nextState = init;
            end
            default: nextState = init;
        endcase
    end

    // Output Logic
    assign valid = (currentState == S01101);
endmodule

//----------------------------------------------Testbench----------------------------------------------//
module tb_detect_sequence;

    // Inputs
    logic clk;
    logic rst_n;
    logic data_in;

    // Outputs
    logic valid;

    // Instantiate the design under test (DUT)
    detect_sequence dut (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(data_in),
        .valid(valid)
    );

    // Clock generation
    always #5 clk = ~clk; // 10ns clock period

    // Coverage
  	covergroup c_group @(posedge clk);
      	option.per_instance=1;
        cp1: coverpoint rst_n;
      	cp2: coverpoint dut.currentState  { bins init = {6'b000001};
                                            bins S1 = {6'b000010};
                                            bins S01 = {6'b000100};
                                            bins S101 = {6'b001000};
                                            bins S1101 = {6'b010000};
                                            bins S01101 = {6'b100000};
                                           	bins others = default;}
    endgroup
  	c_group cg;

    // Test sequence
    initial begin
        // Initialize inputs
        clk = 0;
        rst_n = 0;
        data_in = 0;
      	cg = new();

        // Reset the DUT
        #10 rst_n = 1;

        //---------------------Test case 1: Sequence 01101---------------------//
        #10 data_in = 0;  
        #10 data_in = 1;  
        #10 data_in = 1;  
        #10 data_in = 0;  
        #10 data_in = 1;  
        #10 data_in = 1;  
        #10 data_in = 0;  // valid = 1
        #10;

        //---------------------Test case 2: No sequence detected---------------------//
        #10 data_in = 1;  
        #10 data_in = 0; 
        #10 data_in = 0; 
        #10 data_in = 1; 
        #10 data_in = 1; 
        #10 data_in = 1;  
        #10;

        //---------------------Test case 3: Overlapping sequences---------------------//
        #10 data_in = 0;  
        #10 data_in = 1; 
        #10 data_in = 0; 
        #10 data_in = 1;  
        #10 data_in = 1;  
        #10 data_in = 0;  // Valid = 1
        #10 data_in = 0;  
        #10;

        // End of test
        $finish;
    end

    // Monitor signals
    initial begin
        $monitor("Time=%0t clk=%b rst_n=%b data_in=%b valid=%b state=%b",
                 $time, clk, rst_n, data_in, valid, dut.currentState);
    end

    // Generate waveform
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
    end

    // Sequences
    sequence valid_state;
        $onehot(dut.currentState) && (dut.currentState == 6'b000001 || dut.currentState == 6'b000010 || dut.currentState == 6'b000100 || dut.currentState == 6'b001000 || dut.currentState == 6'b010000 || dut.currentState == 6'b100000);
    endsequence

    sequence valid_transition;
        (dut.currentState == 6'b000001 && (!data_in && dut.nextState == 6'b000001 || data_in && dut.nextState == 6'b000010)) ||
        (dut.currentState == 6'b000010 && (!data_in && dut.nextState == 6'b000100 || data_in && dut.nextState == 6'b000010)) ||
        (dut.currentState == 6'b000100 && (!data_in && dut.nextState == 6'b000001 || data_in && dut.nextState == 6'b001000)) ||
        (dut.currentState == 6'b001000 && (!data_in && dut.nextState == 6'b000100 || data_in && dut.nextState == 6'b010000)) ||
        (dut.currentState == 6'b010000 && (!data_in && dut.nextState == 6'b100000 || data_in && dut.nextState == 6'b000010)) ||
        (dut.currentState == 6'b100000 && dut.nextState == 6'b000001);
    endsequence

    sequence valid_output;
        dut.currentState == 6'b100000;
    endsequence

    sequence output_duration;
        valid ##1 !valid; 
    endsequence

    // Property
    property check_valid_state;
        @(posedge clk) valid_state;
    endproperty

    property check_valid_transitions;
        @(posedge clk) valid_transition;
    endproperty

    property check_valid_output;
        @(posedge clk) valid |-> valid_output;
    endproperty

    property check_output_duration;
        @(posedge clk) output_duration;
    endproperty

    // Assertions
    assert property (check_valid_state)
        else $error("FSM is not in a valid one-hot encoded state!");

    assert property (check_valid_transitions)
        else $error("Invalid transition");

    assert property (check_valid_output)
        else $error("Output valid is high for an incorrect state!");

    assert property (check_output_duration)
        else $error("Output valid is high for more than one cycle!");

endmodule
