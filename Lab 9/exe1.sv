//-------------------------------------------------Arbiter-------------------------------------------------//
module arbiter(
    input clk, rst_n,
    input req1, req2, req3, req4,
    output logic gnt1, gnt2, gnt3, gnt4
);
    always@(posedge clk) begin
        if(!rst_n) begin
            gnt1 <= 1'b0;
            gnt2 <= 1'b0;
            gnt3 <= 1'b0;
            gnt4 <= 1'b0;
        end
        else begin
            
        end
    end 
endmodule